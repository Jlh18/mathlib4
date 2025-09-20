import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

universe v u

noncomputable section

namespace CategoryTheory

open Category Limits MorphismProperty

namespace Poly

variable {C : Type u} [Category.{v} C]

section

variable (R : MorphismProperty C)

notation E " ⟶("R") " B => (p : E ⟶ B) ×' R p

variable [R.IsStableUnderComposition] [R.HasPullbacks] [R.IsStableUnderBaseChange]

@[simps!]
def toComma {T : C} (hT : IsTerminal T) : C ⥤ Comma (𝟭 C) (Functor.fromPUnit T) where
  obj X := {
    left := X
    right := ⟨⟨⟩⟩
    hom := hT.from X }
  map f := {
    left := f
    right := 𝟙 _
    w := by simp }
  map_id := by aesop
  map_comp := by aesop

def Over.topEquivalence [R.HasObjects] {T : C} (hT : IsTerminal T) : R.Over ⊤ T ≌ C where
  functor := MorphismProperty.Over.forget _ _ _ ⋙ CategoryTheory.Over.forget _
  inverse := Comma.lift (toComma hT)
    (by intro; apply HasObjects.obj_mem _ hT) (by simp) (by simp)
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

variable {R} {E B : C}

-- π-clans
variable [R.IsClosedUnderPushforward]

instance (p : E ⟶(R) B) {W : C} (h : W ⟶ B) : HasPullback p.1 h :=
  HasPullbacks.hasPullback h p.2

instance (p : E ⟶(R) B) {W : C} (h : W ⟶ B) : HasPullback h p.1 :=
  hasPullback_symmetry _ _

def mvPoly {I O E B : C} (i : E ⟶(R) I) (p : E ⟶(R) B) (o : B ⟶(R) O) :
    R.Over ⊤ I ⥤ R.Over ⊤ O :=
  MorphismProperty.Over.pullback R _ i.1 ⋙
  Over.IsClosedUnderPushforward.pushforward R p.1 p.2 ⋙
  MorphismProperty.Over.map ⊤ o.2

variable [R.HasObjects]

def ofHasObjects {T : C} (hT : IsTerminal T) (X : C) : X ⟶(R) T :=
  ⟨hT.from X, HasObjects.obj_mem _ hT⟩

def uvPoly' {T : C} (hT : IsTerminal T) (p : E ⟶(R) B) : C ⥤ C :=
  (Over.topEquivalence R hT).inverse ⋙
  mvPoly (ofHasObjects hT E) p (ofHasObjects hT B) ⋙
  (Over.topEquivalence R hT).functor

def uvPoly [HasTerminal C] (p : E ⟶(R) B) : C ⥤ C :=
  (Over.topEquivalence R terminalIsTerminal).inverse ⋙
  mvPoly (ofHasObjects terminalIsTerminal E) p (ofHasObjects terminalIsTerminal B) ⋙
  (Over.topEquivalence R terminalIsTerminal).functor

/-- The action of a univariate polynomial on objects. -/
def uvPolyObj [HasTerminal C] (p : E ⟶(R) B) : C → C := (uvPoly p).obj

@[inherit_doc]
infix:90 " @ " => uvPolyObj

instance {I O E B : C} (i : E ⟶(R) I) (p : E ⟶(R) B) (o : B ⟶(R) O)  :
    Limits.PreservesLimitsOfShape WalkingCospan (mvPoly i p o) := by
  sorry

instance [HasTerminal C] (p : E ⟶(R) B) :
    Limits.PreservesLimitsOfShape WalkingCospan (uvPoly p) := by
  unfold uvPoly
  infer_instance

variable (B)

/-- The identity polynomial functor in single variable. -/
@[simps!]
def id [R.IsomorphismsLe] : B ⟶(R) B := ⟨𝟙 B, isomorphisms_le P _ ⟩

/-- The functor associated to the identity polynomial is isomorphic to the identity functor. -/
def idIso : (UvPoly.id B).functor ≅ star B ⋙ forget B :=
  isoWhiskerRight (isoWhiskerLeft _ (pushforwardIdIso B)) (forget B)

/-- Evaluating the identity polynomial at an object `X` is isomorphic to `B × X`. -/
def idApplyIso (X : C) : (id B) @ X ≅ B ⨯ X := sorry

variable {B}

/-- The fstProjection morphism from `∑ b : B, X ^ (E b)` to `B` again. -/
def fstProj (P : UvPoly E B) (X : C) : P @ X ⟶ B :=
  ((Over.star E ⋙ pushforward P.p).obj X).hom

@[reassoc (attr := simp)]
lemma map_fstProj {X Y : C} (P : UvPoly E B) (f : X ⟶ Y) :
    P.functor.map f ≫ P.fstProj Y = P.fstProj X := by
  simp [fstProj, functor]

/-- A vertical map `ρ : P.p ⟶ Q.p` of polynomials (i.e. a commutative triangle)
```
    ρ
E ----> F
 \     /
  \   /
   \ /
    B
```
induces a natural transformation `Q.functor ⟶ P.functor ` obtained by pasting the following 2-cells
```
              Q.p
C --- >  C/F ----> C/B -----> C
|         |          |        |
|   ↙     | ρ*  ≅    |   =    |
|         v          v        |
C --- >  C/E ---->  C/B ----> C
              P.p
```
-/
def verticalNatTrans {F : C} (P : UvPoly E B) (Q : UvPoly F B) (ρ : E ⟶ F) (h : P.p = ρ ≫ Q.p) :
    Q.functor ⟶ P.functor := by
  have sq : CommSq ρ P.p Q.p (𝟙 _) := by simp [h]
  let cellLeft := (Over.starPullbackIsoStar ρ).hom
  let cellMid := (pushforwardPullbackTwoSquare ρ P.p Q.p (𝟙 _) sq)
  let cellLeftMidPasted := TwoSquare.whiskerRight (cellLeft ≫ₕ cellMid) (Over.pullbackId).inv
  simpa using (cellLeftMidPasted ≫ₕ (vId (forget B)))

/-- A cartesian map of polynomials
```
           P.p
      E -------->  B
      |            |
   φ  |            | δ
      v            v
      F -------->  D
           Q.p
```
induces a natural transformation between their associated functors obtained by pasting the following
2-cells
```
              Q.p
C --- >  C/F ----> C/D -----> C
|         |          |        |
|   ↗     | φ*  ≅    | δ* ↗   |
|         v          v        |
C --- >  C/E ---->  C/B ----> C
              P.p
```
-/
def cartesianNatTrans {D F : C} (P : UvPoly E B) (Q : UvPoly F D)
    (δ : B ⟶ D) (φ : E ⟶ F) (pb : IsPullback P.p φ δ Q.p) : P.functor ⟶ Q.functor :=
  let cellLeft : TwoSquare (𝟭 C) (Over.star F) (Over.star E) (pullback φ) :=
    (Over.starPullbackIsoStar φ).inv
  let cellMid :  TwoSquare (pullback φ) (pushforward Q.p) (pushforward P.p) (pullback δ) :=
    (pushforwardPullbackIsoSquare pb.flip).inv
  let cellRight : TwoSquare (pullback δ) (forget D) (forget B) (𝟭 C) :=
    pullbackForgetTwoSquare δ
  let := cellLeft ≫ᵥ cellMid ≫ᵥ cellRight
  this

open NatTrans in
theorem isCartesian_cartesianNatTrans {D F : C} (P : UvPoly E B) (Q : UvPoly F D)
    (δ : B ⟶ D) (φ : E ⟶ F) (pb : IsPullback P.p φ δ Q.p) :
    NatTrans.IsCartesian (cartesianNatTrans P Q δ φ pb) :=
  (isCartesian_of_isIso _).vComp <|
  (isCartesian_of_isIso _).vComp <|
  isCartesian_pullbackForgetTwoSquare _

/-- A morphism from a polynomial `P` to a polynomial `Q` is a pair of morphisms `e : E ⟶ E'`
and `b : B ⟶ B'` such that the diagram
```
      E -- P.p ->  B
      ^            |
   ρ  |            |
      |     ψ      |
      Pb --------> B
      |            |
   φ  |            | δ
      v            v
      F -- Q.p ->  D
```
is a pullback square. -/
structure Hom {F D : C} (P : UvPoly E B) (Q : UvPoly F D) where
  Pb : C
  δ : B ⟶ D
  φ : Pb ⟶ F
  ψ : Pb ⟶ B
  ρ : Pb ⟶ E
  is_pb : IsPullback ψ φ δ Q.p
  w : ρ ≫ P.p = ψ

namespace Hom

open IsPullback

/-- The identity morphism in the category of polynomials. -/
def id (P : UvPoly E B) : Hom P P := ⟨E, 𝟙 B, 𝟙 _ , P.p , 𝟙 _, IsPullback.of_id_snd, by simp⟩

-- def vertCartExchange

/-- The composition of morphisms in the category of polynomials. -/
def comp {E B F D N M : C} {P : UvPoly E B} {Q : UvPoly F D} {R : UvPoly N M}
    (f : Hom P Q) (g : Hom Q R) : Hom P R := sorry

end Hom

/-- Bundling up the the polynomials over different bases to form the underlying type of the
category of polynomials. -/
structure Total (C : Type*) [Category C] [HasPullbacks C] where
  {E B : C}
  (poly : UvPoly E B)

def Total.of (P : UvPoly E B) : Total C := Total.mk P

end UvPoly

open UvPoly

/-- The category of polynomial functors in a single variable. -/
instance : Category (UvPoly.Total C) where
  Hom P Q := UvPoly.Hom P.poly Q.poly
  id P := UvPoly.Hom.id P.poly
  comp := UvPoly.Hom.comp
  id_comp := by
    simp [UvPoly.Hom.comp]
    sorry
  comp_id := by
    simp [UvPoly.Hom.comp]
    sorry
  assoc := by
    simp [UvPoly.Hom.comp]

def Total.ofHom {E' B' : C} (P : UvPoly E B) (Q : UvPoly E' B') (α : P.Hom Q) :
    Total.of P ⟶ Total.of Q := sorry

namespace UvPoly

variable {C : Type u} [Category.{v} C] [HasTerminal C] [HasPullbacks C]

instance : SMul C (Total C) where
  smul S P := Total.of (smul S P.poly)

/-- Scaling a polynomial `P` by an object `S` is isomorphic to the product of `const S` and the
polynomial `P`. -/
@[simps!]
def smul_eq_prod_const [HasBinaryCoproducts C] [HasInitial C] (S : C) (P : Total C) :
    S • P ≅ Total.of ((const S).prod P.poly) where
  hom := sorry
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

variable {E B : C}

namespace PartialProduct

open PartialProduct

/-- The counit of the adjunction `pullback P.p ⊣ pushforward P.p` evaluated `(star E).obj X`. -/
def ε (P : UvPoly E B) (X : C) : pullback (P.fstProj X) P.p ⟶ E ⨯ X :=
  ((ev P.p).app ((star E).obj X)).left

/-- The partial product fan associated to a polynomial `P : UvPoly E B` and an object `X : C`. -/
@[simps -isSimp]
def fan (P : UvPoly E B) (X : C) : Fan P.p X where
  pt := P @ X
  fst := P.fstProj X
  snd := ε P X ≫ prod.snd -- ((forgetAdjStar E).counit).app X

attribute [simp] fan_pt fan_fst

/--
`P.PartialProduct.fan` is in fact a limit fan; this provides the univeral mapping property of the
polynomial functor.
-/
def isLimitFan (P : UvPoly E B) (X : C) : IsLimit (fan P X) where
  lift c := (pushforwardCurry <| overPullbackToStar c.fst c.snd).left
  fac_left := by aesop_cat (add norm fstProj)
  fac_right := by
    intro c
    simp only [fan_snd, pullbackMap, ε, ev, ← assoc, ← comp_left]
    simp_rw [homMk_eta]
    erw [← homEquiv_counit]
    simp [← ExponentiableMorphism.homEquiv_apply_eq, overPullbackToStar_prod_snd]
  uniq := by
    intro c m h_left h_right
    dsimp [pushforwardCurry]
    symm
    rw [← homMk_left m (U := Over.mk c.fst) (V := Over.mk (P.fstProj X))]
    congr 1
    apply (Adjunction.homEquiv_apply_eq (adj P.p) (overPullbackToStar c.fst c.snd) (Over.homMk m)).mpr
    simp [overPullbackToStar, Fan.overPullbackToStar, Fan.over]
    apply (Adjunction.homEquiv_apply_eq _ _ _).mpr
    rw [← h_right]
    simp [forgetAdjStar, comp_homEquiv, Comonad.adj]
    simp [Equivalence.toAdjunction, homEquiv]
    simp [coalgebraEquivOver, Equivalence.symm]; rfl

end PartialProduct

open PartialProduct

/-- Morphisms `b : Γ ⟶ B` and `e : pullback b P.p ⟶ X` induce a morphism `Γ ⟶ P @ X` which is the
lift of the partial product fan. -/
-- used to be called `pairPoly`
abbrev lift {Γ X : C} (P : UvPoly E B) (b : Γ ⟶ B) (e : pullback b P.p ⟶ X) :
    Γ ⟶ P @ X :=
  partialProd.lift ⟨fan P X, isLimitFan P X⟩ b e

@[simp]
theorem lift_fst {Γ X : C} {P : UvPoly E B} {b : Γ ⟶ B} {e : pullback b P.p ⟶ X} :
    P.lift b e ≫ P.fstProj X = b := partialProd.lift_fst ..

@[reassoc]
theorem lift_snd {Γ X : C} {P : UvPoly E B} {b : Γ ⟶ B} {e : pullback b P.p ⟶ X} :
    comparison (c := fan P X) (P.lift b e) ≫ (fan P X).snd =
    (pullback.congrHom (partialProd.lift_fst b e) rfl).hom ≫ e := partialProd.lift_snd ..

theorem hom_ext {Γ X : C} {P : UvPoly E B} {f g : Γ ⟶ P @ X}
    (h₁ : f ≫ P.fstProj X = g ≫ P.fstProj X)
    (h₂ : comparison f ≫ (fan P X).snd =
      (pullback.congrHom (by exact h₁) rfl).hom ≫ comparison g ≫ (fan P X).snd) :
    f = g := partialProd.hom_ext ⟨fan P X, isLimitFan P X⟩ h₁ h₂

/-- A morphism `f : Γ ⟶ P @ X` projects to a morphism `b : Γ ⟶ B` and a morphism
`e : pullback b P.p ⟶ X`. -/
-- formerly `polyPair`
def proj {Γ X : C} (P : UvPoly E B) (f : Γ ⟶ P @ X) :
    Σ b : Γ ⟶ B, pullback b P.p ⟶ X :=
  ⟨fan P X |>.extend f |>.fst, fan P X |>.extend f |>.snd⟩

@[simp]
theorem proj_fst {Γ X : C} {P : UvPoly E B} {f : Γ ⟶ P @ X} :
    (proj P f).fst = f ≫ P.fstProj X := rfl

/-- The second component of `proj` is a comparison map of pullbacks composed with `ε P X ≫ prod.snd` -/
-- formerly `polyPair_snd_eq_comp_u₂'`
@[simp]
theorem proj_snd {Γ X : C} {P : UvPoly E B} {f : Γ ⟶ P @ X} :
    (proj P f).snd = pullback.map _ _ _ _ f (𝟙 E) (𝟙 B) (by simp) (by simp) ≫ (fan P X).snd := by
  simp [proj]

/-- The domain of the composition of two polynomials. See `UvPoly.comp`. -/
def compDom {E B D A : C} (P : UvPoly E B) (Q : UvPoly D A) :=
  Limits.pullback Q.p (fan P A).snd

@[simps!]
def comp [HasPullbacks C] [HasTerminal C]
    {E B D A : C} (P : UvPoly E B) (Q : UvPoly D A) : UvPoly (compDom P Q) (P @ A) where
  p := pullback.snd Q.p (fan P A).snd ≫ pullback.fst (fan P A).fst P.p
  exp := sorry

/-- The associated functor of the composition of two polynomials is isomorphic to the composition of the associated functors. -/
def compFunctorIso [HasPullbacks C] [HasTerminal C]
    {E B D C : C} (P : UvPoly E B) (Q : UvPoly D C) :
    P.functor ⋙ Q.functor ≅ (comp P Q).functor := by
  sorry

instance monoidal [HasPullbacks C] [HasTerminal C] : MonoidalCategory (UvPoly.Total C) where
  tensorObj X Y := ⟨comp X.poly Y.poly⟩
  whiskerLeft X Y₁ Y₂ := sorry
  whiskerRight := sorry
  tensorUnit := sorry
  associator := sorry
  leftUnitor := sorry
  rightUnitor := sorry

end UvPoly
end CategoryTheory
end

end Poly
end CategoryTheory

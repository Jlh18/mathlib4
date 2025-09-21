import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

universe v u

noncomputable section

namespace CategoryTheory

open Category Limits MorphismProperty MorphismProperty.Over

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

@[simps]
def Over.equivalenceOfHasObjects' (R : MorphismProperty C) [R.HasObjects]
    {X : C} (hX : IsTerminal X) : R.Over ⊤ X ≌ Over X where
  functor := MorphismProperty.Over.forget _ _ _
  inverse := Comma.lift (𝟭 _) (by intro; apply HasObjects.obj_mem _ hX) (by simp) (by simp)
  unitIso := eqToIso rfl
  counitIso := eqToIso rfl
  functor_unitIso_comp := by simp

@[simp]
def Over.equivalenceOfHasObjects (R : MorphismProperty C) [R.HasObjects]
    {X : C} (hX : IsTerminal X) : R.Over ⊤ X ≌ C :=
  (equivalenceOfHasObjects' R hX).trans (Over.equivalenceOfIsTerminal hX)

notation E " ⟶("R") " B => { p : E ⟶ B // R p }

/-- A class of maps `P` that is stable under base change is also stable under pushforward
if whenever pullbacks along `f` exist and `f` satisfies `P`,
the pullback functor `Over.pullback P ⊤ f` is a left adjoint. -/
class IsClosedUnderPushforward (P : MorphismProperty C) :
    Prop extends P.IsStableUnderBaseChange where
  pullback_isLeftAdjoint {X Y : C} (f : X ⟶ Y) (h : P f)
  [∀ {W : C} (h : W ⟶ Y), HasPullback h f] : (Over.pullback P ⊤ f).IsLeftAdjoint

instance (P : MorphismProperty C) [P.IsClosedUnderPushforward]
    {X Y : C} (f : X ⟶(P) Y) [∀ {W : C} (h : W ⟶ Y), HasPullback h f.1] :
    (Over.pullback P ⊤ f.1).IsLeftAdjoint :=
  IsClosedUnderPushforward.pullback_isLeftAdjoint f.1 f.2

/-- A chosen right adjoint to the pullback functor. -/
def Over.IsClosedUnderPushforward.pushforward
    (P : MorphismProperty C) [P.IsClosedUnderPushforward]
    {X Y : C} (f : X ⟶(P) Y) [∀ {W : C} (h : W ⟶ Y), HasPullback h f.1] :
    P.Over ⊤ X ⥤ P.Over ⊤ Y :=
  (Over.pullback P ⊤ f.1).rightAdjoint

end MorphismProperty

/-- `P : UvPoly C` is a polynomial functors in a single variable -/
structure MvPoly (R : MorphismProperty C) (I O E B : C) where
  (i : E ⟶(R) I)
  (p : E ⟶(R) B)
  (o : B ⟶(R) O)

namespace MvPoly

variable {R : MorphismProperty C} {E B : C}

@[simps]
def Over.mk (p : E ⟶(R) B) : R.Over ⊤ B where
  left := E
  right := ⟨⟨⟩⟩
  hom := p.1
  prop := p.2

@[simps]
def Over.Hom.mk {p q : R.Over ⊤ B} (left : p.left ⟶ q.left) (hleft : left ≫ q.hom = p.hom) :
    p ⟶ q where
  left := left
  right := eqToHom (by simp)
  w := by simp [hleft]
  prop_hom_left := trivial
  prop_hom_right := trivial

variable [R.IsStableUnderComposition] [hR : R.HasPullbacks] [R.IsStableUnderBaseChange]
-- ∧ [R.HasObjects] ∧ [R.IsomorphismsLe] = clan

variable [R.IsClosedUnderPushforward]
-- clan ∧ [R.IsClosedUnderPushforward] = π-clan

instance (p : E ⟶(R) B) {W : C} (h : W ⟶ B) : HasPullback p.1 h :=
  hR.hasPullback h p.2

instance (p : E ⟶(R) B) {W : C} (h : W ⟶ B) : HasPullback h p.1 :=
  hasPullback_symmetry _ _

instance : (⊤ : MorphismProperty C).HasOfPostcompProperty ⊤ where
  of_postcomp := by simp

instance (p : E ⟶(R) B) : (MorphismProperty.Over.pullback R ⊤ p.1).IsRightAdjoint :=
  (mapPullbackAdj R ⊤ p.1 p.2 ⟨⟩).isRightAdjoint

instance (p : E ⟶(R) B) : (IsClosedUnderPushforward.pushforward R p).IsRightAdjoint := by
  dsimp [IsClosedUnderPushforward.pushforward]
  infer_instance

variable {I O E B : C}

def functor (P : MvPoly R I O E B) :
    R.Over ⊤ I ⥤ R.Over ⊤ O :=
  pullback R ⊤ P.i.1 ⋙
  IsClosedUnderPushforward.pushforward R P.p ⋙
  map ⊤ P.o.2

/-- The action of a univariate polynomial on objects. -/
def apply (P : MvPoly R I O E B) : R.Over ⊤ I → R.Over ⊤ O := (functor P).obj

@[inherit_doc]
infix:90 " @ " => apply

/--
Convert an object `p` in `R.Over ⊤ B` to a morphism in `R.Over ⊤ O` by composing with `o`.
     p
 E -----> B
  \      /
   \    /o
    \  /
     VV
     O
-/
@[simp]
def Over.drop (p : R.Over ⊤ B) (o : B ⟶(R) O) :
    (map ⊤ o.2).obj p ⟶ Over.mk o :=
  Over.Hom.mk p.hom (by simp)

/-- The first projection morphism from `P @ X = ∑ b : B, X ^ (E b)` to `B`,
where `o` is represented by its domain `B` and `i` is represented by its domain `E`. -/
def fstProj (P : MvPoly R I O E B) (X : R.Over ⊤ I) : P @ X ⟶ Over.mk P.o :=
  Over.drop ((MorphismProperty.Over.pullback R ⊤ P.i.1 ⋙
    Over.IsClosedUnderPushforward.pushforward R P.p).obj X) P.o

@[reassoc (attr := simp)]
lemma map_fstProj (P : MvPoly R I O E B) {X Y : R.Over ⊤ I} (f : X ⟶ Y) :
    (functor P).map f ≫ fstProj P Y = fstProj P X := by
  ext
  simp [fstProj, functor]

instance {I O E B : C} (P : MvPoly R I O E B) : Limits.PreservesLimitsOfShape WalkingCospan
    (MorphismProperty.Over.map ⊤ P.o.2) := by sorry

instance {I O E B : C} (P : MvPoly R I O E B) :
    Limits.PreservesLimitsOfShape WalkingCospan (MvPoly.functor P) := by
  dsimp [functor]
  infer_instance

end MvPoly

abbrev UvPoly (R : MorphismProperty C) (E B : C) := E ⟶(R) B

namespace UvPoly

section

variable {R : MorphismProperty C} {E B : C}

variable [R.IsStableUnderComposition] [R.HasPullbacks] [R.IsStableUnderBaseChange]
-- ∧ [R.HasObjects] = clan

variable [R.IsClosedUnderPushforward]
-- clan ∧ [R.IsClosedUnderPushforward] = π-clan

variable [HasTerminal C] [R.HasObjects]

def object (X : C) : X ⟶(R) ⊤_ C :=
  ⟨terminal.from X, HasObjects.obj_mem _ terminalIsTerminal⟩

def mvPoly (p : E ⟶(R) B) : MvPoly R (⊤_ C) (⊤_ C) E B where
  i := object E
  p := p
  o := object B

def functor (p : E ⟶(R) B) : C ⥤ C :=
  (equivalenceOfHasObjects R terminalIsTerminal).inverse ⋙
  MvPoly.functor (mvPoly p) ⋙
  (equivalenceOfHasObjects R terminalIsTerminal).functor

/-- The action of a univariate polynomial on objects. -/
def apply [HasTerminal C] (p : E ⟶(R) B) : C → C := (functor p).obj

@[inherit_doc]
infix:90 " @ " => apply

instance [HasTerminal C] (p : E ⟶(R) B) :
    Limits.PreservesLimitsOfShape WalkingCospan (functor p) := by
  unfold functor
  infer_instance

variable (B)

/-- The identity polynomial functor in single variable. -/
@[simps!]
def id [R.IsomorphismsLe] : B ⟶(R) B := ⟨𝟙 B, isomorphisms_le R _ ⟩

variable {B}

/-- The fstProjection morphism from `∑ b : B, X ^ (E b)` to `B` again. -/
def fstProj (P : E ⟶(R) B) (X : C) : P @ X ⟶ B :=
  (equivalenceOfHasObjects R terminalIsTerminal).functor.map <|
    (mvPoly P).fstProj ((equivalenceOfHasObjects R terminalIsTerminal).inverse.obj X)

@[reassoc (attr := simp)]
lemma map_fstProj (P : E ⟶(R) B) {X Y : C} (f : X ⟶ Y) :
    (functor P).map f ≫ fstProj P Y = fstProj P X := by
  simp only [fstProj, functor, Functor.comp_map, ← Functor.map_comp]
  simp

#exit
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

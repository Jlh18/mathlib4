/-
Copyright (c) 2025 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua, Sina Hazratpour, Emily Riehl
-/

import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Functor.TwoSquare
import Mathlib.CategoryTheory.NatTrans.IsCartesian
import Mathlib.CategoryTheory.Comma.Over.Pushforward

universe v u

noncomputable section

namespace CategoryTheory

open Category Limits MorphismProperty

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (P : MorphismProperty C)

abbrev OverTop (X : C) := P.Over ⊤ X

namespace OverTop

@[simps]
def equivalenceOfHasObjects' (R : MorphismProperty C) [R.HasObjects]
    {X : C} (hX : IsTerminal X) : R.OverTop X ≌ Over X where
  functor := MorphismProperty.Over.forget _ _ _
  inverse := Comma.lift (𝟭 _) (by intro; apply HasObjects.obj_mem _ hX) (by simp) (by simp)
  unitIso := eqToIso rfl
  counitIso := eqToIso rfl
  functor_unitIso_comp := by simp

@[simp]
def equivalenceOfHasObjects (R : MorphismProperty C) [R.HasObjects]
    {X : C} (hX : IsTerminal X) : R.OverTop X ≌ C :=
  (equivalenceOfHasObjects' R hX).trans (Over.equivalenceOfIsTerminal hX)

abbrev pullback (P : MorphismProperty C) [P.IsStableUnderBaseChange]
    {E B} (f : E ⟶ B) [P.HasPullback f] := MorphismProperty.Over.pullback P ⊤ f

abbrev map {P : MorphismProperty C} [P.IsStableUnderComposition]
    {X Y : C} {f : X ⟶ Y} (hPf : P f) :=
  MorphismProperty.Over.map ⊤ hPf

variable {P : MorphismProperty C} {E B : C}

@[simps]
def mk (p : E ⟶(P) B) : P.OverTop B where
  left := E
  right := ⟨⟨⟩⟩
  hom := p.1
  prop := p.2

@[simps]
def homMk {p q : P.OverTop B} (left : p.left ⟶ q.left) (hleft : left ≫ q.hom = p.hom) :
    p ⟶ q where
  left := left
  right := eqToHom (by simp)
  w := by simp [hleft]
  prop_hom_left := trivial
  prop_hom_right := trivial

/--
Convert an object `p` in `R.OverTop B` to a morphism in `R.OverTop O` by composing with `o`.
     p
 E -----> B
  \      /
   \    /o
    \  /
     VV
     O
-/
@[simp]
def homOfMorphismProperty [P.IsStableUnderComposition] {O} (p : P.OverTop B) (o : B ⟶(P) O) :
    (map o.2).obj p ⟶ OverTop.mk o :=
  Over.homMk p.hom (by simp)

end OverTop


open OverTop

/-- A class of maps `P` that is stable under base change is also stable under pushforward
if whenever pullbacks of maps in `P` along `f` exist,
the pullback functor `Over.pullback P ⊤ f` is a left adjoint. -/
class IsStableUnderPushforward : Prop extends P.IsStableUnderBaseChange where
  pullback_isLeftAdjoint {X Y : C} (f : X ⟶ Y) [P.HasPullback f] :
  (pullback P f).IsLeftAdjoint

/-- A chosen right adjoint to the pullback functor. -/
noncomputable def OverTop.pushforward [P.IsStableUnderBaseChange]
    {X Y : C} (f : X ⟶ Y) [P.HasPullback f]
    (hf : (MorphismProperty.Over.pullback P ⊤ f).IsLeftAdjoint) :
    P.OverTop X ⥤ P.OverTop Y :=
  (pullback P f).rightAdjoint

abbrev Exponentiable (P : MorphismProperty C) [P.IsStableUnderBaseChange]
    {E B} (f : E ⟶ B) [P.HasPullback f] :=
  P.HasPushforward f

section Exponentiable

variable (P : MorphismProperty C) [P.IsStableUnderBaseChange] {X Y : C} (f : X ⟶ Y)
    [P.HasPullback f] [P.Exponentiable f]

/-- A chosen right adjoint to the pullback functor. -/
def pushforward : P.OverTop X ⥤ P.OverTop Y :=
  (pullback P f).rightAdjoint

/-- The `pullback ⊣ pushforward` adjunction. -/
def pullbackPushforwardAdjunction : Over.pullback P ⊤ f ⊣ pushforward P f :=
  Adjunction.ofIsLeftAdjoint (pullback P f)

/-- The dependent evaluation natural transformation as the counit of the adjunction. -/
abbrev ev : pushforward P f ⋙ pullback P f ⟶ 𝟭 _ :=
  pullbackPushforwardAdjunction P f |>.counit

end Exponentiable

/-- A class of maps `P` that is stable under base change is also stable under pushforward
if whenever pullbacks along `f` exist and `f` satisfies `P`,
the pullback functor `pullback P f` is a left adjoint.

Note that this alone does not assert existence of pushforwards of all `P`-maps along `P`-maps.
By also assuming `[P.HasPullbacks]` one can deduce existence of pushforwards of all
`P`-maps along `P`-maps.
-/
class IsClosedUnderPushforward (P : MorphismProperty C) :
    Prop extends P.IsStableUnderBaseChange where
  pullback_isLeftAdjoint {X Y : C} (f : X ⟶(P) Y) [P.HasPullback f.1] :
  P.Exponentiable f.1

instance (P : MorphismProperty C) [P.IsClosedUnderPushforward]
    {X Y : C} (f : X ⟶(P) Y) [P.HasPullback f.1] : P.Exponentiable f.1 :=
  IsClosedUnderPushforward.pullback_isLeftAdjoint f

/-- A chosen right adjoint to the pullback functor. -/
def IsClosedUnderPushforward.pushforward (P : MorphismProperty C) [P.IsClosedUnderPushforward]
    {X Y : C} (f : X ⟶(P) Y) [P.HasPullback f.1] : P.OverTop X ⥤ P.OverTop Y :=
  (pullback P f.1).rightAdjoint

end MorphismProperty

open OverTop

/-- `P : MvPoly C` is a multivariate polynomial functor
         p
      E ---> B
  i ↙         ↘ o
  I               O

We can lazily read this as `∑ b : B, X ^ (E b)`,
for some `X` in the (`P`-restricted) slice over `I`.

In full detail:
Viewing such an `X` as a series of variables `X_k` indexed by `k ∈ I`,
and `B` as a family of types `B_k` indexed by `j ∈ O`
this can be further viewed as `O`-many `I`-ary polynomials `∑ b : B_j, X_(i b) ^ (E b)`
-/
structure MvPoly (R : MorphismProperty C) [R.HasPullbacks] [R.IsStableUnderBaseChange]
    (I O E B : C) where
  (i : E ⟶(R) I)
  (p : E ⟶(R) B)
  (exp : R.Exponentiable p.1 := by infer_instance)
  (o : B ⟶(R) O)

namespace MvPoly

variable {R : MorphismProperty C}
variable [R.IsStableUnderComposition] [R.HasPullbacks] [R.IsStableUnderBaseChange]
variable {E B : C}

instance : (⊤ : MorphismProperty C).HasOfPostcompProperty ⊤ where
  of_postcomp := by simp

instance (p : E ⟶(R) B) : (pullback R p.1).IsRightAdjoint :=
  (MorphismProperty.Over.mapPullbackAdj R ⊤ p.1 p.2 ⟨⟩).isRightAdjoint

instance (p : E ⟶(R) B) (exp : (pullback R p.1).IsLeftAdjoint) :
    (pushforward R p.1 exp).IsRightAdjoint := by
  dsimp [OverTop.pushforward]
  infer_instance

variable {I O E B : C} (P : MvPoly R I O E B)

instance : R.Exponentiable P.p.fst := P.exp

def functor (P : MvPoly R I O E B) :
    R.OverTop I ⥤ R.OverTop O :=
  pullback R P.i.1 ⋙ pushforward R P.p.1 P.exp ⋙ map P.o.2

/-- The action of a univariate polynomial on objects. -/
def apply (P : MvPoly R I O E B) : R.OverTop I → R.OverTop O := (functor P).obj

@[inherit_doc]
infix:90 " @ " => apply

/-- (Ignoring the indexing from `i` and `o`)
This is the first projection morphism from `P @ X = ∑ b : B, X ^ (E b)` to `B`,
as an object in the `P`-restricted slice over `B`. -/
abbrev fstProj' (P : MvPoly R I O E B) (X : R.OverTop I) : R.OverTop B :=
  (pullback R P.i.1 ⋙ pushforward R P.p.1 P.exp).obj X

/-- This is the first projection morphism from `P @ X = ∑ b : B, X ^ (E b)` to `B`,
as a morphism in the `P`-restricted slice over `O`. -/
def fstProj (P : MvPoly R I O E B) (X : R.OverTop I) : P @ X ⟶ OverTop.mk P.o :=
  OverTop.homOfMorphismProperty (fstProj' P X) P.o

@[reassoc (attr := simp)]
lemma map_fstProj (P : MvPoly R I O E B) {X Y : R.OverTop I} (f : X ⟶ Y) :
    (functor P).map f ≫ fstProj P Y = fstProj P X := by
  ext
  simp [fstProj, functor]

/--
The two right adjoints compose to give a new right adjoint
`pullback R P.i.1 ⋙ pushforward R P.p.1 P.exp`.
`rightAdjunction` is said adjunction `pullback p ⋙ map i ⊣ pullback i ⋙ pushforward p`.
-/
def rightAdjunction : pullback R P.p.1 ⋙ OverTop.map P.i.2
    ⊣ pullback R P.i.1 ⋙ pushforward R P.p.1 P.exp :=
  Adjunction.comp (Adjunction.ofIsLeftAdjoint (pullback R P.p.fst))
    (MorphismProperty.Over.mapPullbackAdj R ⊤ P.i.fst _ trivial)

/-- The counit of the adjunction `pullback p ⋙ map i ⊣ pullback i ⋙ pushforward p` evaluated at `X`.
Ignoring the indexing from `i` and `o`,
this can be viewed as the second projection morphism from `P @ X = ∑ b : B, X ^ (E b)`
to `X^ (E b)`.
-/
def sndProj (P : MvPoly R I O E B) (X : R.OverTop I) :
    (pullback R P.p.1 ⋙ map P.i.2).obj (fstProj' P X) ⟶ X :=
  (rightAdjunction P).counit.app X

namespace Equiv

variable (P : MvPoly R I O E B)

def fst {Γ} {X} (pair : Γ ⟶ P @ X) : R.OverTop B := by
  have := (pair ≫ fstProj P X).left
  dsimp at this
  refine OverTop.mk ⟨ (pair ≫ fstProj P X).left , ?_ ⟩
  sorry

end Equiv

instance {I O E B : C} (P : MvPoly R I O E B) : Limits.PreservesLimitsOfShape WalkingCospan
    (MorphismProperty.Over.map ⊤ P.o.2) := by sorry

instance {I O E B : C} (P : MvPoly R I O E B) :
    Limits.PreservesLimitsOfShape WalkingCospan (MvPoly.functor P) := by
  dsimp [functor]
  infer_instance

end MvPoly

structure UvPoly (R : MorphismProperty C) [R.HasPullbacks] [R.IsStableUnderBaseChange]
    (E B : C) where
  (p : E ⟶(R) B)
  (exp : (MorphismProperty.Over.pullback R ⊤ p.1).IsLeftAdjoint := by infer_instance)

namespace UvPoly

section

variable {R : MorphismProperty C} {E B : C}

variable [HasTerminal C]

variable [R.IsStableUnderComposition] [R.HasPullbacks] [R.IsStableUnderBaseChange] [R.HasObjects]

/-- Given a π-clan `R`, any `R`-map is a signature for a polynomial functor. -/
def ofIsClosedUnderPushforward [R.IsClosedUnderPushforward] (p : E ⟶(R) B) : UvPoly R E B where
  p := p
  exp := IsClosedUnderPushforward.pullback_isLeftAdjoint p

def object (X : C) : X ⟶(R) ⊤_ C :=
  ⟨terminal.from X, HasObjects.obj_mem _ terminalIsTerminal⟩

def mvPoly (P : UvPoly R E B) : MvPoly R (⊤_ C) (⊤_ C) E B where
  i := object E
  p := P.p
  exp := P.exp
  o := object B

def functor (P : UvPoly R E B) : C ⥤ C :=
  (equivalenceOfHasObjects R terminalIsTerminal).inverse ⋙
  MvPoly.functor P.mvPoly ⋙
  (equivalenceOfHasObjects R terminalIsTerminal).functor

/-- The action of a univariate polynomial on objects. -/
def apply [HasTerminal C] (P : UvPoly R E B) : C → C := P.functor.obj

@[inherit_doc]
infix:90 " @ " => apply

instance [HasTerminal C] (P : UvPoly R E B) :
    Limits.PreservesLimitsOfShape WalkingCospan P.functor := by
  unfold functor
  infer_instance

variable (B)

/-- The identity polynomial functor in single variable. -/
@[simps!]
def id [R.IsomorphismsLe] : B ⟶(R) B := ⟨𝟙 B, isomorphisms_le R _ ⟩

variable {B}

/-- The fstProjection morphism from `∑ b : B, X ^ (E b)` to `B` again. -/
def fstProj (P : UvPoly R E B) (X : C) : P @ X ⟶ B :=
  (equivalenceOfHasObjects R terminalIsTerminal).functor.map <|
    P.mvPoly.fstProj ((equivalenceOfHasObjects R terminalIsTerminal).inverse.obj X)

@[reassoc (attr := simp)]
lemma map_fstProj (P : UvPoly R E B) {X Y : C} (f : X ⟶ Y) :
    P.functor.map f ≫ fstProj P Y = fstProj P X := by
  simp only [fstProj, functor, Functor.comp_map, ← Functor.map_comp]
  simp

open TwoSquare

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
def verticalNatTrans {F : C} (P : UvPoly R E B) (Q : UvPoly R F B) (ρ : E ⟶ F)
    (h : P.p.1 = ρ ≫ Q.p.1) : Q.functor ⟶ P.functor := sorry --by
  -- have sq : CommSq ρ P.p.1 Q.p.1 (𝟙 _) := by simp [h]
  -- let cellLeft := (Over.starPullbackIsoStar ρ).hom
  -- let cellMid := (pushforwardPullbackTwoSquare ρ P.p Q.p (𝟙 _) sq)
  -- let cellLeftMidPasted := TwoSquare.whiskerRight (cellLeft ≫ₕ cellMid) (Over.pullbackId).inv
  -- simpa using (cellLeftMidPasted ≫ₕ (vId (forget B)))

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
def cartesianNatTrans {D F : C} (P : UvPoly R E B) (Q : UvPoly R F D)
    (δ : B ⟶ D) (φ : E ⟶ F) (pb : IsPullback P.p.1 φ δ Q.p.1) : P.functor ⟶ Q.functor :=
  sorry
  -- let cellLeft : TwoSquare (𝟭 C) (Over.star F) (Over.star E) (pullback φ) :=
  --   (Over.starPullbackIsoStar φ).inv
  -- let cellMid :  TwoSquare (pullback φ) (pushforward Q.p) (pushforward P.p) (pullback δ) :=
  --   (pushforwardPullbackIsoSquare pb.flip).inv
  -- let cellRight : TwoSquare (pullback δ) (forget D) (forget B) (𝟭 C) :=
  --   pullbackForgetTwoSquare δ
  -- let := cellLeft ≫ᵥ cellMid ≫ᵥ cellRight
  -- this

theorem isCartesian_cartesianNatTrans {D F : C} (P : UvPoly R E B) (Q : UvPoly R F D)
    (δ : B ⟶ D) (φ : E ⟶ F) (pb : IsPullback P.p.1 φ δ Q.p.1) :
    (cartesianNatTrans P Q δ φ pb).IsCartesian := by
  sorry
  -- simp [cartesianNatTrans]
  -- infer_instance

  -- (isCartesian_of_isIso _).vComp <|
  -- (isCartesian_of_isIso _).vComp <|
  -- isCartesian_pullbackForgetTwoSquare _

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
structure Hom {F D : C} (P : UvPoly R E B) (Q : UvPoly R F D) where
  Pb : C
  δ : B ⟶ D
  φ : Pb ⟶ F
  ψ : Pb ⟶ B
  ρ : Pb ⟶ E
  is_pb : IsPullback ψ φ δ Q.p.1
  w : ρ ≫ P.p.1 = ψ

namespace Hom

open IsPullback

/-- The identity morphism in the category of polynomials. -/
def id (P : UvPoly R E B) : Hom P P := ⟨E, 𝟙 B, 𝟙 _ , P.p.1 , 𝟙 _, IsPullback.of_id_snd, by simp⟩

-- def vertCartExchange

/-- The composition of morphisms in the category of polynomials. -/
def comp {E B F D N M : C} {P : UvPoly R E B} {Q : UvPoly R F D} {R : UvPoly R N M}
    (f : Hom P Q) (g : Hom Q R) : Hom P R := sorry

end Hom

open UvPoly

variable {E B : C}

namespace PartialProduct

open PartialProduct

#exit
/-- The counit of the adjunction `pullback P.p ⊣ pushforward P.p` evaluated `(star E).obj X`. -/
def ε (P : UvPoly R E B) (X : C) : Limits.pullback P.p.1 (P.fstProj X) ⟶ E ⨯ X :=
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

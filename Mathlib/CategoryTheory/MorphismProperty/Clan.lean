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

namespace Over

@[simps]
def equivalenceOfHasObjects' (R : MorphismProperty C) [R.HasObjects]
    {X : C} (hX : IsTerminal X) : R.Over ⊤ X ≌ Over X where
  functor := MorphismProperty.Over.forget _ _ _
  inverse := Comma.lift (𝟭 _) (by intro; apply HasObjects.obj_mem _ hX) (by simp) (by simp)
  unitIso := eqToIso rfl
  counitIso := eqToIso rfl
  functor_unitIso_comp := by simp

@[simp]
def equivalenceOfHasObjects (R : MorphismProperty C) [R.HasObjects]
    {X : C} (hX : IsTerminal X) : R.Over ⊤ X ≌ C :=
  (equivalenceOfHasObjects' R hX).trans (Over.equivalenceOfIsTerminal hX)

variable {P : MorphismProperty C} {E B : C}

@[simps]
def ofMorphismProperty (p : E ⟶(P) B) : P.Over ⊤ B where
  left := E
  right := ⟨⟨⟩⟩
  hom := p.1
  prop := p.2

@[simps]
def homMkTop {p q : P.Over ⊤ B} (left : p.left ⟶ q.left) (hleft : left ≫ q.hom = p.hom) :
    p ⟶ q where
  left := left
  right := eqToHom (by simp)
  w := by simp [hleft]
  prop_hom_left := trivial
  prop_hom_right := trivial

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
def homOfMorphismProperty [P.IsStableUnderComposition] {O} (p : P.Over ⊤ B) (o : B ⟶(P) O) :
    (map ⊤ o.2).obj p ⟶ Over.ofMorphismProperty o :=
  Over.homMk p.hom (by simp)

end Over

end MorphismProperty

open MorphismProperty.Over

/-- `P : MvPoly R H I O` is a multivariate polynomial functor consisting of the following maps
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

To explain the need for two morphism properties,
consider the following two use-cases:
1. `R = ⊤` is all maps and the category has all pullbacks.
  `H` is the class of exponentiable maps - it follows from all maps having pullbacks that `H`
  also has pullbacks.
2. `R = H` is a π-clan, [see Joyal, def 2.4.1](https://arxiv.org/pdf/1710.10238).

This will typically be used with the following instances

- For pullback of `R`-maps along `i`, `p` and `o` we need
  `[R.IsStableUnderBaseChange] [R.HasPullbacks]`
- For the left adjoint to pullback for `o` we need `[R.IsStableUnderComposition]`
- For pushforward of `R`-maps along `p` we need
  `[R.IsStableUnderPushforward H] [R.HasPushforwards H]`
- For pushforward of `R`-maps along `p` we also assume `[H.HasPullbacks]`.
  This is useful - it makes the `R`-restricted pushforward of `R`-maps along `p`
  a partial left adjoint to *global* pullback along `p`,
  ```
        pushforward p
   R.Over E -----> R.Over B
      |              |
      |       ⊥      |
      |              |
      V              V
     C/E <--------- C/B
         pullback p
  ```
  which is strictly stronger than just having a left adjoint to `R`-restricted pullback
  `(pullback : R.Over B ⥤ R.Over E) ⊣ (pushforward : R.Over E ⥤ R.Over B)`.
-/
structure MvPoly (R : MorphismProperty C) (H : MorphismProperty C) (I O : C) where
  (E B : C)
  (i : E ⟶(R) I)
  (p : E ⟶(H) B)
  (o : B ⟶(R) O)

namespace MvPoly

instance : (⊤ : MorphismProperty C).HasOfPostcompProperty ⊤ where
  of_postcomp := by simp

variable {R : MorphismProperty C} {H : MorphismProperty C}

instance {B O : C} (i : B ⟶(R) O) [R.HasPullbacks] [R.IsStableUnderBaseChange]
    [R.IsStableUnderComposition] : (pullback R ⊤ i.1).IsRightAdjoint :=
  (mapPullbackAdj R ⊤ i.1 i.2 ⟨⟩).isRightAdjoint

variable {I O : C} (P : MvPoly R H I O) [R.HasPullbacks] [R.IsStableUnderBaseChange]
    [R.IsStableUnderComposition] [H.HasPullbacks] [R.HasPushforwards H]
    [R.IsStableUnderPushforward H]

def functor : R.Over ⊤ I ⥤ R.Over ⊤ O :=
  pullback R ⊤ P.i.1 ⋙ MorphismProperty.pushforward R P.p ⋙ map ⊤ P.o.2

/-- The action of a univariate polynomial on objects. -/
def apply (P : MvPoly R H I O) : R.Over ⊤ I → R.Over ⊤ O := (functor P).obj

@[inherit_doc]
infix:90 " @ " => apply

open PolynomialPartialAdjunction

/-- (Ignoring the indexing from `i` and `o`)
This is the first projection morphism from `P @ X = ∑ b : B, X ^ (E b)` to `B`,
as an object in the `P`-restricted slice over `B`. -/
abbrev fstProj (P : MvPoly R H I O) (X : R.Over ⊤ I) : R.Over ⊤ P.B :=
  (partialRightAdjoint P.i.1 P.p).obj X

@[reassoc (attr := simp)]
lemma map_fstProj (P : MvPoly R H I O) {X Y : R.Over ⊤ I} (f : X ⟶ Y) :
    ((partialRightAdjoint P.i.1 P.p).map f).left ≫ (fstProj P Y).hom = (fstProj P X).hom := by
  simp

/-- The counit of the adjunction `pullback p ⋙ map i ⊣ pullback i ⋙ pushforward p` evaluated at `X`.
Ignoring the indexing from `i` and `o`,
this can be viewed as the second projection morphism from `P @ X = ∑ b : B, X ^ (E b)`
to `X^ (E b)`.
-/
def sndProj (P : MvPoly R H I O) (X : R.Over ⊤ I) :
    (leftAdjoint P.i.1 P.p).obj (fstProj P X).toComma ⟶ X.toComma :=
  (counit P.i.1 P.p).app X

namespace Equiv

variable {P : MvPoly R H I O} {Γ : Over O} {X : R.Over ⊤ I}

def fst (pair : Γ ⟶ (P @ X).toComma) : Over P.B := Over.mk (pair.left ≫ (fstProj P X).hom)

abbrev sndDom (pair : Γ ⟶ (P @ X).toComma) : Over I := (leftAdjoint P.i.1 P.p).obj (fst pair)

def snd (pair : Γ ⟶ (P @ X).toComma) : sndDom pair ⟶ X.toComma :=
  homEquiv P.i.1 P.p (Over.homMk (pair.left))

lemma snd_eq (pair : Γ ⟶ (P @ X).toComma) : snd pair =
    (leftAdjoint P.i.1 P.p).map (Over.homMk (pair.left)) ≫ sndProj P X := by
  erw [Equiv.apply_eq_iff_eq_symm_apply, ← homEquiv_comp_symm]
  simp [sndProj, counit]

def mk (f : Over P.B) (hf : Γ = (Over.map P.o.1).obj f)
    (s : (leftAdjoint P.i.1 P.p).obj f ⟶ X.toComma) :
    Γ ⟶ (P @ X).toComma :=
  eqToHom hf ≫ (Over.map P.o.fst).map ((homEquiv P.i.1 P.p).symm s)

@[simp]
lemma fst_mk (f : Over P.B) (hf : Γ = (Over.map P.o.1).obj f)
    (s : (leftAdjoint P.i.1 P.p).obj f ⟶ X.toComma) : fst (mk f hf s) = f := by
  subst hf; simp [fst, mk]; rfl

lemma snd_mk (f : Over P.B) (hf : Γ = (Over.map P.o.1).obj f)
    (s : (leftAdjoint P.i.1 P.p).obj f ⟶ X.toComma) : snd (mk f hf s) =
    eqToHom (by simp) ≫ s := calc snd (mk f hf s)
  _ = (leftAdjoint P.i.1 P.p).map (eqToHom (fst_mk f hf s)) ≫ s := by
    erw [Equiv.apply_eq_iff_eq_symm_apply, ← homEquiv_comp_symm]
    ext
    simp [mk]
  _ = eqToHom _ ≫ s := by
    simp only [eqToHom_map]

@[simp]
lemma map_fst (pair : Γ ⟶ (P @ X).toComma) : (Over.map P.o.fst).obj (fst pair) = Γ := by
  have := pair.w
  simp only [Functor.id_obj, Functor.const_obj_obj, Functor.id_map,
    CostructuredArrow.right_eq_id, Functor.const_obj_map, comp_id] at this
  simp [Over.map, Comma.mapRight, fst]
  congr

@[simp]
lemma eta (pair : Γ ⟶ (P @ X).toComma) : mk (fst pair) (by simp) (snd pair) = pair := by
  ext
  simp [mk, snd]

end Equiv

instance (P : MvPoly R H I O) : Limits.PreservesLimitsOfShape WalkingCospan
    (MorphismProperty.Over.map ⊤ P.o.2) := by sorry

instance (P : MvPoly R H I O) :
    Limits.PreservesLimitsOfShape WalkingCospan (MvPoly.functor P) := by
  dsimp [functor]
  have : (MorphismProperty.Over.pullback R ⊤ P.i.1).IsRightAdjoint :=
    Adjunction.isRightAdjoint (MorphismProperty.Over.mapPullbackAdj R ⊤ P.i.1 P.i.2 trivial)
  infer_instance

end MvPoly

/-- `P : UvPoly R E B` is the type of signatures for polynomial functors
         p
      E ---> B

We read this as `∑ b : B, X ^ (E b)`,
for some `R`-object `X` (meaning the unique map to the terminal object is in `R`).

This notion of polynomial makes sense when `R` is a π-clan,
[see Joyal, def 2.4.1](https://arxiv.org/pdf/1710.10238).
Therefore it will typically be used with the following instances

- For pullback of `R`-maps along `p` we need
  `[R.IsStableUnderBaseChange] [R.HasPullbacks]`
- For the left adjoint to pullback along `B`, we assume `[R.IsStableUnderComposition]`
  and `[R.HasObjects]`, meaning the unique map `B ⟶ ⊤_ C` is in `R`.
  For this, we will also assume `[HasTerminal C]`.
- For pushforward of `R`-maps along `p` we need
  `[R.IsStableUnderPushforward R] [R.HasPushforwards R]`
- For pushforward of `R`-maps along `p` we also assume `[R.HasPullbacks]`.
  This is useful - it makes the `R`-restricted pushforward of `R`-maps along `p`
  a partial left adjoint to *global* pullback along `p`,
  ```
        pushforward p
   R.Over E -----> R.Over B
      |              |
      |       ⊥      |
      |              |
      V              V
     C/E <--------- C/B
         pullback p
  ```
  which is strictly stronger than just having a left adjoint to `R`-restricted pullback
  `(pullback : R.Over B ⥤ R.Over E) ⊣ (pushforward : R.Over E ⥤ R.Over B)`.
-/
structure UvPoly (R : MorphismProperty C) (E B : C) where
  (p : E ⟶(R) B)

namespace UvPoly

section

variable {R : MorphismProperty C} {E B : C}

variable [HasTerminal C]

variable [R.IsStableUnderComposition] [R.HasPullbacks] [R.IsStableUnderBaseChange] [R.HasObjects]
  [R.IsStableUnderPushforward R] [R.HasPushforwards R]

def object (X : C) : X ⟶(R) ⊤_ C :=
  ⟨terminal.from X, HasObjects.obj_mem _ terminalIsTerminal⟩

@[simp]
abbrev toOverTerminal : C ⥤ R.Over ⊤ (⊤_ C) :=
  (equivalenceOfHasObjects R terminalIsTerminal).inverse

@[simp]
abbrev fromOverTerminal : R.Over ⊤ (⊤_ C) ⥤ C :=
  (equivalenceOfHasObjects R terminalIsTerminal).functor

@[simps]
def mvPoly (P : UvPoly R E B) : MvPoly R R (⊤_ C) (⊤_ C) where
  E := E
  B := B
  i := object E
  p := P.p
  o := object B

def functor (P : UvPoly R E B) : C ⥤ C :=
  toOverTerminal ⋙
  MvPoly.functor P.mvPoly ⋙
  fromOverTerminal

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
  (P.mvPoly.fstProj (toOverTerminal.obj X)).hom

@[reassoc (attr := simp)]
lemma map_fstProj (P : UvPoly R E B) {X Y : C} (f : X ⟶ Y) :
    P.functor.map f ≫ fstProj P Y = fstProj P X :=
  P.mvPoly.map_fstProj (toOverTerminal.map f)

/-- The second projection morphism from `P @ X = ∑ b : B, X ^ (E b)` to `X^ (E b)`. -/
def sndProj (P : UvPoly R E B) (X : C) :
    Limits.pullback (fstProj P X) P.p.1 ⟶ X :=
  (P.mvPoly.sndProj (toOverTerminal.obj X)).left

open TwoSquare

/-- A vertical map `ρ : P.p.1 ⟶ Q.p.1` of polynomials (i.e. a commutative triangle)
```
    ρ
E ----> F
 \     /
  \   / \ /
    B
```
induces a natural transformation `Q.functor ⟶ P.functor ` obtained by pasting the following 2-cells
```
              Q.p.1
C --- >  C/F ----> C/B -----> C
|         |          |        |
|   ↙     | ρ*  ≅    |   =    |
|         v          v        |
C --- >  C/E ---->  C/B ----> C
              P.p.1
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

/-- The domain of the composition of two polynomials. See `UvPoly.comp`. -/
def compDom {E B E' B' : C} (P : UvPoly R E B) (P' : UvPoly R E' B') : C :=
  sorry
  -- Limits.pullback P'.p (fan P A).snd

@[simps!]
def comp {E B E' B' : C} (P : UvPoly R E B) (P' : UvPoly R E' B') :
    UvPoly R (compDom P P') (P @ B') where
  p := sorry -- pullback.snd Q.p (fan P A).snd ≫ pullback.fst (fan P A).fst P.p


namespace Equiv

variable {P : UvPoly R E B} {Γ X Y : C}

/-- Convert the morphism `pair` into a morphism in the over category `Over (⊤_ C)` -/
@[simp]
abbrev fstAux (pair : Γ ⟶ P @ X) : Over.mk (terminal.from Γ) ⟶
    ((toOverTerminal ⋙ MvPoly.functor P.mvPoly).obj X).toComma := Over.homMk pair

def fst (pair : Γ ⟶ P @ X) : Γ ⟶ B :=
  (MvPoly.Equiv.fst (fstAux pair)).hom

lemma fst_eq (pair : Γ ⟶ P @ X) : fst pair = pair ≫ P.fstProj X := by
  aesop_cat

def snd (pair : Γ ⟶ P @ X) : Limits.pullback (fst pair) P.p.1 ⟶ X :=
  (MvPoly.Equiv.snd (fstAux pair)).left

lemma snd_eq (pair : Γ ⟶ P @ X) : snd pair =
    Limits.pullback.map (fst pair) P.p.1 (P.fstProj X) P.p.1 pair (𝟙 E) (𝟙 B) (by simp [fst_eq])
    (by simp) ≫ sndProj P X := by
  simpa [Limits.pullback.map] using congrArg CommaMorphism.left (MvPoly.Equiv.snd_eq (fstAux pair))

def snd' (pair : Γ ⟶ P @ X) {R f g} (H : IsPullback (P := R) f g (fst pair) P.p.1) : R ⟶ X :=
  H.isoPullback.hom ≫ snd pair

theorem snd_eq_snd' (pair : Γ ⟶ P @ X) :
    snd pair = snd' pair (.of_hasPullback ..) := by simp [snd']; sorry
    -- simp lemma in HoTTLean ForMathlib

/-- Convert the morphism `x` into a morphism in the over category `Over (⊤_ C)` -/
@[simp]
abbrev mkAux (b : Γ ⟶ B) (x : pullback b P.p.1 ⟶ X) :
    (PolynomialPartialAdjunction.leftAdjoint P.mvPoly.i.fst P.mvPoly.p).obj (Over.mk b) ⟶
    ((toOverTerminal (R := R)).obj X).toComma :=
    -- Over.mk (terminal.from (pullback b P.p.1)) ⟶ ((toOverTerminal (R := R)).obj X).toComma :=
  Over.homMk x

def mk (b : Γ ⟶ B) (x : pullback b P.p.1 ⟶ X) : Γ ⟶ P @ X :=
  (MvPoly.Equiv.mk (P := P.mvPoly) (Γ := Over.mk (terminal.from Γ))
    (Over.mk b) (by congr; apply terminal.hom_ext) (mkAux b x)).left

def mk' (b : Γ ⟶ B) {R f g} (H : IsPullback (P := R) f g b P.p.1) (x : R ⟶ X) : Γ ⟶ P @ X :=
  mk b (H.isoPullback.inv ≫ x)

theorem mk_eq_mk' (b : Γ ⟶ B) (x : pullback b P.p.1 ⟶ X) :
    mk b x = mk' b (.of_hasPullback ..) x := by simp [mk']; sorry

@[simp]
lemma fst_mk (b : Γ ⟶ B) (x : pullback b P.p.1 ⟶ X) :
    fst (mk b x) = b := by
  simp only [fst, mk, Over.homMk_eta]
  rw! (castMode := .all) [MvPoly.Equiv.fst_mk]
  simp [← heq_eq_eq]; rfl

@[simp]
lemma fst_mk' (b : Γ ⟶ B) {R f g} (H : IsPullback (P := R) f g b P.p.1) (x : R ⟶ X) :
    fst (mk' b H x) = b := by
  simp [mk']

@[simp]
lemma mk'_comp_fstProj (b : Γ ⟶ B) {R f g} (H : IsPullback (P := R) f g b P.p.1) (x : R ⟶ X) :
    mk' b H x ≫ P.fstProj X = b := by
  simp [← fst_eq]

theorem fst_comp_left (pair : Γ ⟶ P @ X) {Δ} (f : Δ ⟶ Γ) :
    fst (f ≫ pair) = f ≫ fst pair := by simp [fst_eq]

theorem fst_comp_right (pair : Γ ⟶ P @ X) (f : X ⟶ Y) :
    fst (pair ≫ P.functor.map f) = fst pair := by
  simp [fst_eq]

lemma snd'_eq (pair : Γ ⟶ P @ X) {R f g} (H : IsPullback (P := R) f g (fst pair) P.p.1) :
    snd' pair H = pullback.lift (f ≫ pair) g (by simpa using H.w) ≫ sndProj P X := by
  rw [snd', snd_eq, ← Category.assoc]
  congr 1
  ext <;> simp

/-- Switch the selected pullback `R` used in `UvPoly.Equiv.snd'` with a different pullback `R'`. -/
lemma snd'_eq_snd' (pair : Γ ⟶ P @ X) {R f g} (H : IsPullback (P := R) f g (fst pair) P.p.1)
    {R' f' g'} (H' : IsPullback (P := R') f' g' (fst pair) P.p.1) :
    snd' pair H = (H.isoIsPullback _ _ H').hom ≫ snd' pair H' := by
  simp [snd'_eq, ← Category.assoc]
  congr 2
  ext <;> simp

@[simp]
lemma snd'_mk' (b : Γ ⟶ B) {R f g} (H : IsPullback (P := R) f g b P.p.1) (x : R ⟶ X) :
    snd' (mk' b H x) (by rwa [fst_mk']) = x := by
  sorry
  -- have : comparison (c := fan P X) (mk' P X b H x) ≫ _ =
  --     (pullback.congrHom (f₁ := mk' P X b H x ≫ _) ..).hom ≫ _ :=
  --   partialProd.lift_snd ⟨fan P X, isLimitFan P X⟩ b (H.isoPullback.inv ≫ x)
  -- have H' : IsPullback (P := R) f g (mk' P X b H x ≫ (fan P X).fst) P.p.1 := by simpa
  -- convert congr(H'.isoPullback.hom ≫ $(this)) using 1
  -- · simp [partialProd.snd, partialProd.cone, snd'_eq]
  --   simp only [← Category.assoc]; congr! 2
  --   simp [comparison]; ext <;> simp
  -- · slice_rhs 1 0 => skip
  --   refine .symm <| .trans ?_ (Category.id_comp _); congr! 1
  --   rw [Iso.comp_inv_eq_id]; ext <;> simp

lemma snd_mk_heq (b : Γ ⟶ B) (x : pullback b P.p.1 ⟶ X) :
    snd (mk b x) ≍ x := by
  sorry
  -- have h := mk_eq_mk' P X b x
  -- set t := mk' P ..
  -- have : snd' P X t _ = x := snd'_mk' ..
  -- refine .trans ?_ this.heq
  -- rw [snd_eq_snd']; congr! 2 <;> simp

lemma snd_mk (b : Γ ⟶ B) (x : pullback b P.p.1 ⟶ X) :
    snd (mk b x) = eqToHom (by simp) ≫ x := by
  apply eq_of_heq; rw [heq_eqToHom_comp_iff]; apply snd_mk_heq

theorem snd'_comp_left (pair : Γ ⟶ P @ X)
    {R f g} (H : IsPullback (P := R) f g (fst pair) P.p.1)
    {Δ} (σ : Δ ⟶ Γ)
    {R' f' g'} (H' : IsPullback (P := R') f' g' (σ ≫ fst pair) P.p.1) :
    snd' (σ ≫ pair) (by convert H'; rw [fst_comp_left]) =
    H.lift (f' ≫ σ) g' (by simp [H'.w]) ≫ snd' pair H := by
  simp only [snd'_eq, ← Category.assoc]
  congr 2
  ext
  · simp
  · simp

theorem snd'_comp_right (pair : Γ ⟶ P @ X) (f : X ⟶ Y)
    {R f1 f2} (H : IsPullback (P := R) f1 f2 (fst pair) P.p.1) :
    snd' (pair ≫ P.functor.map f) (by rwa [fst_comp_right]) =
    snd' pair H ≫ f := by
  sorry
  -- simp [snd'_eq, fan_snd, ε]
  -- have := congr($((ExponentiableMorphism.ev P.p.1).naturality ((Over.star E).map f)).left ≫ prod.snd)
  -- dsimp at this; simp at this
  -- rw [← this]; clear this
  -- simp only [← Category.assoc]; congr! 2
  -- ext <;> simp
  -- · slice_rhs 2 3 => apply pullback.lift_fst
  --   slice_rhs 1 2 => apply pullback.lift_fst
  --   simp; rfl
  -- · slice_rhs 2 3 => apply pullback.lift_snd
  --   symm; apply pullback.lift_snd

theorem snd_comp_right (pair : Γ ⟶ P @ X) (f : X ⟶ Y) : snd (pair ≫ P.functor.map f) =
    eqToHom (by congr 1; apply fst_comp_right) ≫ snd pair ≫ f := by
  -- rw [snd_eq_snd', snd'_comp_right, snd', Category.assoc, ← eqToIso.hom]; congr! 2
  -- exact IsPullback.isoPullback_eq_eqToIso_left (fst_comp_right _ _ _ f pair) P.p.1
  sorry

lemma ext' {pair₁ pair₂ : Γ ⟶ P @ X}
    {R f g} (H : IsPullback (P := R) f g (fst pair₁) P.p.1)
    (h1 : fst pair₁ = fst pair₂)
    (h2 : snd' pair₁ H = snd' pair₂ (by rwa [h1] at H)) :
    pair₁ = pair₂ := by
  -- simp [fst_eq] at h1 H
  -- apply partialProd.hom_ext ⟨fan P X, isLimitFan P X⟩ h1
  -- refine (cancel_epi H.isoPullback.hom).1 ?_
  -- convert h2 using 1 <;> (
  --   simp [snd'_eq, comparison_pullback.map, partialProd.snd, partialProd.cone]
  --   simp only [← Category.assoc]; congr! 2
  --   ext <;> simp)
  -- · slice_lhs 2 3 => apply pullback.lift_fst
  --   slice_lhs 1 2 => apply H.isoPullback_hom_fst
  --   simp
  -- · slice_lhs 2 3 => apply pullback.lift_snd
  --   slice_lhs 1 2 => apply H.isoPullback_hom_snd
  --   simp
  sorry

/-- Switch the selected pullback `R` used in `UvPoly.Equiv.mk'` with a different pullback `R'`. -/
theorem mk'_eq_mk' (b : Γ ⟶ B) {R f g} (H : IsPullback (P := R) f g b P.p.1) (x : R ⟶ X)
    {R' f' g'} (H' : IsPullback (P := R') f' g' b P.p.1) :
    mk' b H x = mk' b H' ((IsPullback.isoIsPullback _ _ H H').inv ≫ x) := by
  -- apply ext' P X (R := R) (f := f) (g := g) (by convert H; simp)
  -- · rw [snd'_eq_snd' P X (mk' P X b H' ((IsPullback.isoIsPullback _ _ H H').inv ≫ x))
  --     (by convert H; simp) (by convert H'; simp)]
  --   simp [snd'_mk']
  -- · simp
  sorry

@[simp]
lemma eta' (pair : Γ ⟶ P @ X)
    {R f1 f2} (H : IsPullback (P := R) f1 f2 (fst pair) P.p.1) :
    mk' (fst pair) H (snd' pair H) = pair :=
  .symm <| ext' H (by simp) (by simp)

@[simp]
lemma eta (pair : Γ ⟶ P @ X) :
    mk (fst pair) (snd pair) = pair := by
  simp [mk_eq_mk', snd_eq_snd']

lemma mk'_comp_right (b : Γ ⟶ B) {R f1 f2} (H : IsPullback (P := R) f1 f2 b P.p.1) (x : R ⟶ X)
    (f : X ⟶ Y) : mk' b H x ≫ P.functor.map f = mk' b H (x ≫ f) := by
  -- refine .symm <| ext' _ _ (by rwa [fst_mk']) (by simp [fst_comp_right]) ?_
  -- rw [snd'_comp_right (H := by rwa [fst_mk'])]; simp
  sorry

lemma mk_comp_right (b : Γ ⟶ B) (x : pullback b P.p.1 ⟶ X) (f : X ⟶ Y) :
    mk b x ≫ P.functor.map f = mk b (x ≫ f) := by
  simp [mk_eq_mk', mk'_comp_right]

theorem mk'_comp_left {Δ}
    (b : Γ ⟶ B) {R f g} (H : IsPullback (P := R) f g b P.p.1) (x : R ⟶ X) (σ : Δ ⟶ Γ)
    (σb) (eq : σ ≫ b = σb)
    {R' f' g'} (H' : IsPullback (P := R') f' g' σb P.p.1) :
    σ ≫ UvPoly.Equiv.mk' b H x = UvPoly.Equiv.mk' σb H'
    (H.lift (f' ≫ σ) g' (by simp [eq, H'.w]) ≫ x) := by
  apply ext' (f := f') (g := g') (H := by convert H'; simp [eq, fst_eq])
  · rw [snd'_comp_left (H := by convert H; rw [fst_mk']) (H' := by convert H'; rw [← eq, fst_mk'])]
    simp
  · simp [eq, fst_comp_left]

theorem mk_comp_left {Δ} (b : Γ ⟶ B) (x : pullback b P.p.1 ⟶ X) (σ: Δ ⟶ Γ) :
    σ ≫ UvPoly.Equiv.mk b x =
    UvPoly.Equiv.mk (σ ≫ b)
      (pullback.map _ _ _ _ σ (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ x) := by
  simp only [mk_eq_mk']
  rw [mk'_comp_left (H := .of_hasPullback _ _) (H' := .of_hasPullback _ _) (eq := rfl)]
  congr 2; ext <;> simp

-- lemma mk'_comp_cartesianNatTrans_app {E' B' Γ X : C} {P' : UvPoly R E' B'}
--     (y : Γ ⟶ B) (R f g) (H : IsPullback (P := R) f g y P.p.1)
--     (x : R ⟶ X) (e : E ⟶ E') (b : B ⟶ B')
--     (hp : IsPullback P.p.1 e b P'.p.1) :
--     Equiv.mk' y H x ≫ (P.cartesianNatTrans P' b e hp).app X =
--     Equiv.mk' P' X (y ≫ b) (H.paste_vert hp) x := by
--   have : fst P' X (Equiv.mk' P X y H x ≫ (P.cartesianNatTrans P' b e hp).app X) = y ≫ b := by
--     rw [fst_eq, Category.assoc, cartesianNatTrans_fstProj, ← Category.assoc, mk'_comp_fstProj]
--   refine ext' _ _ (this ▸ H.paste_vert hp) (by simpa) ?_
--   simp; rw [snd'_eq]
--   have := snd'_mk' P X y H x
--   rw [snd'_eq, ← fan_snd_map' _ _ X hp] at this
--   refine .trans ?_ this
--   simp only [← Category.assoc]; congr 1; ext <;> simp

end Equiv

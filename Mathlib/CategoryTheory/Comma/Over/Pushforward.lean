/-
Copyright (c) 2025 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/

import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint

noncomputable section

universe v v₂ u u₂

namespace CategoryTheory

open Category Limits Comonad

variable {C : Type u} [Category.{v} C] (X : C)
variable {D : Type u₂} [Category.{v₂} D]

variable {S S' : C} (f : S ⟶ S') [∀ {W} (h : W ⟶ S'), HasPullback h f]

/-- `Y` is the pushforward of `X` along `f` when it represents the presheaf
`Hom(pullback f (-), X)`. -/
abbrev IsPushforward (X : Over S) (Y : Over S') :=
  ((Over.pullback f).op ⋙ yoneda.obj X).RepresentableBy Y

abbrev HasPushforward (X : Over S) : Prop :=
  ((Over.pullback f).op ⋙ yoneda.obj X).IsRepresentable

abbrev pushforward (X : Over S) [HasPushforward f X] : Over S' :=
  ((Over.pullback f).op ⋙ yoneda.obj X).reprX

def pushforward.isPushforward (X : Over S) [HasPushforward f X] :
    IsPushforward f X (pushforward f X) :=
  ((Over.pullback f).op ⋙ yoneda.obj X).representableBy

abbrev HasPushforwards : Prop := ∀ (X : Over S), HasPushforward f X

namespace Over

variable [HasPushforwards f]

lemma pullback_rightAdjointObjIsDefined_eq_top :
    (Over.pullback f).rightAdjointObjIsDefined = ⊤ := by aesop_cat

instance : (pullback f).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
  (pullback_rightAdjointObjIsDefined_eq_top f)

def pushforward : Over S ⥤ Over S' :=
  (pullback f).rightAdjoint

def pullbackPushforwardAdjunction : pullback f ⊣ pushforward f :=
  Adjunction.ofIsLeftAdjoint (pullback f)

end Over

end CategoryTheory
end

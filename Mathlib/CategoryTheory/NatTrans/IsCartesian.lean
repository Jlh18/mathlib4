/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.TwoSquare
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

open CategoryTheory Limits IsPullback

namespace CategoryTheory

universe v' u' v u v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₅ u₆ u₇ u₈ u₁ u₂ u₃ u₄

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]
variable {K : Type*} [Category K] {D : Type*} [Category D]

namespace NatTrans

open Functor

/-- A natural transformation is *cartesian*
if all its naturality squares are pullbacks. -/
class IsCartesian {F G : J ⥤ C} (α : F ⟶ G) : Prop where
  isCartesian ⦃i j : J⦄ (f : i ⟶ j) : IsPullback (F.map f) (α.app i) (α.app j) (G.map f)

alias isCartesian := IsCartesian.isCartesian

namespace IsCartesian

instance of_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α] : IsCartesian α where
  isCartesian _ _ f := IsPullback.of_vert_isIso ⟨NatTrans.naturality _ f⟩

instance of_isCartesian [HasTerminal J] {F G : J ⥤ C} (α : F ⟶ G) [IsCartesian α]
    [IsIso (α.app (⊤_ J))] : IsIso α := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ α
    (fun j ↦ isIso_snd_of_isIso <| isCartesian <| terminal.from j)

instance of_discrete {ι : Type*} {F G : Discrete ι ⥤ C}
    (α : F ⟶ G) : IsCartesian α where
  isCartesian := by
    rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
    simp only [Discrete.functor_map_id]
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

instance of_isPullback_to_terminal [HasTerminal J] {F G : J ⥤ C} (α : F ⟶ G)
    (pb : ∀ j,
    IsPullback (F.map (terminal.from j)) (α.app j) (α.app (⊤_ J)) (G.map (terminal.from j))) :
    IsCartesian α where
  isCartesian := by
    intro i j f
    apply IsPullback.of_right (h₁₂ := F.map (terminal.from j)) (h₂₂ := G.map (terminal.from j))
    · simpa [← F.map_comp, ← G.map_comp] using (pb i)
    · exact α.naturality f
    · exact pb j

instance comp {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} [IsCartesian α] [IsCartesian β] :
    IsCartesian (α ≫ β) where
  isCartesian _ _ f := (isCartesian f).paste_vert (isCartesian f)

instance whiskerRight {F G : J ⥤ C} {α : F ⟶ G} [IsCartesian α] (H : C ⥤ D)
    [∀ (i j : J) (f : j ⟶ i), PreservesLimit (cospan (α.app i) (G.map f)) H] :
    IsCartesian (whiskerRight α H) where
  isCartesian _ _ f := (isCartesian f).map H

instance whiskerLeft {K : Type*} [Category K] {F G : J ⥤ C}
    {α : F ⟶ G} [IsCartesian α] (H : K ⥤ J) : IsCartesian (whiskerLeft H α) where
  isCartesian _ _ f := isCartesian (H.map f)

instance hcomp {K : Type*} [Category K] {F G : J ⥤ C} {M N : C ⥤ K} {α : F ⟶ G} {β : M ⟶ N}
    [IsCartesian α] [IsCartesian β]
    [∀ (i j : J) (f : j ⟶ i), PreservesLimit (cospan (α.app i) (G.map f)) M] :
    IsCartesian (NatTrans.hcomp α β) where
  isCartesian i j f := by
    simpa using (Functor.whiskerRight α M ≫ Functor.whiskerLeft G β).isCartesian f

open TwoSquare

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
variable {C₅ : Type u₅} {C₆ : Type u₆} {C₇ : Type u₇} {C₈ : Type u₈}
  [Category.{v₅} C₅] [Category.{v₆} C₆] [Category.{v₇} C₇] [Category.{v₈} C₈]
  {T' : C₂ ⥤ C₅} {R' : C₅ ⥤ C₆} {B' : C₄ ⥤ C₆} {L' : C₃ ⥤ C₇} {R'' : C₄ ⥤ C₈} {B'' : C₇ ⥤ C₈}

instance vComp {w : TwoSquare T L R B} {w' : TwoSquare B L' R'' B''}
    [∀ (i j : C₁) (f : j ⟶ i), PreservesLimit (cospan (w.app i) ((L ⋙ B).map f)) R'']
    [IsCartesian w] [IsCartesian w'] : IsCartesian (w ≫ᵥ w') := by
  dsimp only [TwoSquare.vComp]
  infer_instance

instance hComp {w : TwoSquare T L R B} {w' : TwoSquare T' R R' B'}
    [∀ (i j : C₁) (f : j ⟶ i), PreservesLimit (cospan (w.app i) ((L ⋙ B).map f)) B']
    [IsCartesian w] [IsCartesian w'] : IsCartesian (w ≫ₕ w') := by
  dsimp only [TwoSquare.hComp]
  infer_instance

end IsCartesian
end NatTrans

/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joseph Hua
-/
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.Tactic.DepRewrite

/-!
# Adjunction of pushforward and pullback in `P.Over Q X`

Under suitable assumptions on `P`, `Q` and `f`,
a morphism `f : X ⟶ Y` defines two functors:

- `Over.map`: post-composition with `f`
- `Over.pullback`: base-change along `f`

such that `Over.map` is the left adjoint to `Over.pullback`.
We say that `P` is *stable* under pushforward if `Over.pullback`
also is a left adjoint.
We say that `P` is *closed* under pushforward if `Over.pullback`
also is a left adjoint for any `f` satisfying `P`.

-/

namespace CategoryTheory.MorphismProperty

open Limits

variable {T : Type*} [Category T] (P Q : MorphismProperty T) [Q.IsMultiplicative]
variable {X Y Z : T} (f : X ⟶ Y)

section Map

variable {P} [P.IsStableUnderComposition] (hPf : P f)

variable {f}

/-- If `P` is stable under composition and `f : X ⟶ Y` satisfies `P`,
this is the functor `P.Over Q X ⥤ P.Over Q Y` given by composing with `f`. -/
@[simps! obj_left obj_hom map_left]
def Over.map : P.Over Q X ⥤ P.Over Q Y :=
  Comma.mapRight _ (Discrete.natTrans fun _ ↦ f) <| fun X ↦ P.comp_mem _ _ X.prop hPf

lemma Over.map_comp {X Y Z : T} {f : X ⟶ Y} (hf : P f) {g : Y ⟶ Z} (hg : P g) :
    map Q (P.comp_mem f g hf hg) = map Q hf ⋙ map Q hg := by
  fapply Functor.ext
  · simp [map, Comma.mapRight, CategoryTheory.Comma.mapRight, Comma.lift]
  · intro U V k
    ext
    simp

/-- `Over.map` commutes with composition. -/
@[simps! hom_app_left inv_app_left]
def Over.mapComp {X Y Z : T} {f : X ⟶ Y} (hf : P f) {g : Y ⟶ Z} (hg : P g) [Q.RespectsIso] :
    map Q (P.comp_mem f g hf hg) ≅ map Q hf ⋙ map Q hg :=
  NatIso.ofComponents (fun X ↦ Over.isoMk (Iso.refl _))

end Map

section Pullback

variable [∀ {W} (h : W ⟶(P) Y), HasPullback h.1 f]
  [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]

variable {P Q} in
@[simps]
def Over.morphismProperty (f : P.Over Q X) : f.left ⟶(P) X := ⟨ f.hom , f.prop ⟩

instance (A : P.Over Q Y) : HasPullback A.hom f :=
  inferInstanceAs (HasPullback (A.morphismProperty).1 f)

/-- If `P` and `Q` are stable under base change and pullbacks exist in `T`,
this is the functor `P.Over Q Y ⥤ P.Over Q X` given by base change along `f`. -/
@[simps! obj_left obj_hom map_left]
noncomputable def Over.pullback : P.Over Q Y ⥤ P.Over Q X where
  obj A := Over.mk Q (Limits.pullback.snd A.morphismProperty.1 f)
    (baseChange_obj f A.toComma A.prop)
  map {A B} g := Over.homMk (pullback.map _ f _ f g.left (𝟙 _) (𝟙 _) (by simp) (by simp))
    (by simp) (baseChange_map f ⟨g.left, g.right, _⟩ g.prop_hom_left)

variable {P} {Q}

instance (X : P.Over Q Z) (g : Y ⟶ Z) [∀ {W} (h : W ⟶(P) Z), HasPullback h.1 g] :
    HasPullback (pullback.snd X.hom g) f :=
  let p : pullback X.hom g ⟶(P) Y := ⟨pullback.snd X.hom g, pullback_snd _ _ X.prop⟩
  inferInstanceAs (HasPullback p.1 f)

/-- `Over.pullback` commutes with composition. -/
@[simps! hom_app_left inv_app_left]
noncomputable def Over.pullbackComp (g : Y ⟶ Z) [∀ {W} (h : W ⟶(P) Z), HasPullback h.1 g]
    [Q.RespectsIso] : Over.pullback P Q (f ≫ g) ≅ Over.pullback P Q g ⋙ Over.pullback P Q f :=
  NatIso.ofComponents
    (fun X ↦
      Over.isoMk ((pullbackLeftPullbackSndIso X.hom g f).symm) (by simp))

lemma Over.pullbackComp_left_fst_fst (g : Y ⟶ Z) [∀ {W} (h : W ⟶ Z), HasPullback h g]
    [Q.RespectsIso] (A : P.Over Q Z) : ((Over.pullbackComp f g).hom.app A).left ≫
      pullback.fst (pullback.snd A.hom g) f ≫ pullback.fst A.hom g =
        pullback.fst A.hom (f ≫ g) := by
  simp

variable {f}
/-- If `f = g`, then base change along `f` is naturally isomorphic to base change along `g`. -/
noncomputable def Over.pullbackCongr {g : X ⟶ Y} (h : f = g) :
    have {W : T} (k : W ⟶(P) Y) : HasPullback k.1 g := by subst h; infer_instance
    Over.pullback P Q f ≅ Over.pullback P Q g :=
  NatIso.ofComponents (fun X ↦ eqToIso (by simp [h]))

@[reassoc (attr := simp)]
lemma Over.pullbackCongr_hom_app_left_fst {g : X ⟶ Y} (h : f = g) (A : P.Over Q Y) :
    have {W : T} (k : W ⟶(P) Y) : HasPullback k.1 g := by subst h; infer_instance
    ((Over.pullbackCongr h).hom.app A).left ≫ pullback.fst A.hom g =
      pullback.fst A.hom f := by
  subst h
  simp [pullbackCongr]

end Pullback

section Adjunction

variable [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
  [Q.IsStableUnderBaseChange] [∀ {W} (h : W ⟶ Y), HasPullback h f]

/-- `P.Over.map` is left adjoint to `P.Over.pullback` if `f` satisfies `P`. -/
noncomputable def Over.mapPullbackAdj [Q.HasOfPostcompProperty Q] (hPf : P f) (hQf : Q f) :
    Over.map Q hPf ⊣ Over.pullback P Q f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A B ↦
        { toFun := fun g ↦
            Over.homMk (pullback.lift g.left A.hom <| by simp) (by simp) <| by
              apply Q.of_postcomp (W' := Q)
              · exact Q.pullback_fst B.hom f hQf
              · simpa using g.prop_hom_left
          invFun := fun h ↦ Over.homMk (h.left ≫ pullback.fst B.hom f)
            (by
              simp only [map_obj_left, Functor.const_obj_obj, pullback_obj_left, Functor.id_obj,
                Category.assoc, pullback.condition, map_obj_hom, ← pullback_obj_hom, Over.w_assoc])
            (Q.comp_mem _ _ h.prop_hom_left (Q.pullback_fst _ _ hQf))
          left_inv := by cat_disch
          right_inv := fun h ↦ by
            ext
            dsimp
            ext
            · simp
            · simpa using h.w.symm } }

end Adjunction

/-- A class of maps `P` that is stable under base change is also stable under pushforward
if whenever pullbacks of maps in `P` along `f` exist,
the pullback functor `Over.pullback P ⊤ f` is a left adjoint. -/
class IsStableUnderPushforward : Prop extends P.IsStableUnderBaseChange where
  pullback_isLeftAdjoint {X Y : T} (f : X ⟶ Y) [∀ {W : T} (h : W ⟶(P) Y), HasPullback h.1 f] :
  (Over.pullback P ⊤ f).IsLeftAdjoint

/-- A chosen right adjoint to the pullback functor. -/
noncomputable def Over.pushforward [P.IsStableUnderBaseChange]
    {X Y : T} (f : X ⟶ Y) [∀ {W : T} (h : W ⟶(P) Y), HasPullback h.1 f]
    (hf : (MorphismProperty.Over.pullback P ⊤ f).IsLeftAdjoint) :
    P.Over ⊤ X ⥤ P.Over ⊤ Y :=
  (Over.pullback P ⊤ f).rightAdjoint

end CategoryTheory.MorphismProperty

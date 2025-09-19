import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

universe v u

namespace CategoryTheory

open Category Limits

namespace MorphismProperty

variable {C : Type u} [Category.{v} C]

section

-- clans (minus the condition that all objects are fibrant)
variable (P : MorphismProperty C) [P.IsomorphismsLe] [P.IsStableUnderComposition]
  [P.IsStableUnderBaseChange]


-- π-clans
variable [P.IsClosedUnderPushforward]


end


end MorphismProperty
end CategoryTheory

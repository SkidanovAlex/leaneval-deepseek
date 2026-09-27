import Mathlib
import Submission.Work.Drive.goodC_translate

namespace Work.Drive

/-- **The parity core depends only on the set `Zc γ`.**

The definition of `ParityCore γ` mentions `Zc γ` in two roles: as the domain of the function
`b : Zc γ → ZMod 2` (a `Subtype`, hence sensitive to the *type* `Zc γ`) and in the antisymmetry
hypothesis, through the specific proof term `neg_mem_Zc hu : -u ∈ Zc γ`.  Both dependences are
immaterial: the domain is a subtype of `UnitAddCircle`, so it is determined by the underlying set, and
proof terms are irrelevant.

`parityCoreSet` below re-states the notion with `Zc γ` abstracted as an arbitrary set `Z`, the
antisymmetry hypothesis quantified over an *arbitrary* proof `hu' : -u ∈ Z` instead of the specific
`neg_mem_Zc hu`, and the local constancy expressed as `Continuous b`.  `parityCore_iff_set` shows that
the two formulations agree (`parityCore_iff_set` is where proof irrelevance is used, to replace `hu'`
by `neg_mem_Zc hu`), and `parityCoreSet γ` is manifestly a function of the set `Zc γ` alone, so a
`rw` transports it along an equality of sets. -/
def parityCoreSet (Z : Set UnitAddCircle) : Prop :=
  ∃ b : Z → ZMod 2,
    Continuous b ∧
    (∀ (u : UnitAddCircle) (hu : u ∈ Z) (hu' : -u ∈ Z), b ⟨u, hu⟩ + b ⟨-u, hu'⟩ = 1) ∧
    (∀ (a : UnitAddCircle) (ha : a ∈ Z) (c : UnitAddCircle) (hc : c ∈ Z),
      b ⟨a, ha⟩ = 1 → b ⟨c, hc⟩ = 1 → ∀ (h : a + c ∈ Z), b ⟨a + c, h⟩ = 1)

/-- `ParityCore γ` is the same statement as `parityCoreSet (Zc γ)`. -/
theorem parityCore_iff_set (γ : Circle → ℝ × ℝ) :
    ParityCore γ ↔ parityCoreSet (Zc γ) := by
  constructor
  · rintro ⟨b, hcont, hanti, htrans⟩
    exact ⟨b, hcont, fun u hu hu' => by
      rw [show (⟨-u, hu'⟩ : Zc γ) = ⟨-u, neg_mem_Zc hu⟩ from Subtype.ext rfl]
      exact hanti u hu, htrans⟩
  · rintro ⟨b, hcont, hanti, htrans⟩
    exact ⟨b, hcont, fun u hu => hanti u hu (neg_mem_Zc hu), htrans⟩

/-- **The parity core depends only on the set `Zc γ`.**  A general transport lemma: two curves with
the same non-collision set have equivalent parity cores.  (`rw [ParityCore, ParityCore, h]` does not
work directly, because `Zc` occurs inside `Subtype` and inside the membership proof `neg_mem_Zc`;
`parityCore_iff_set` removes both obstructions.) -/
theorem parityCore_congr {γ γ' : Circle → ℝ × ℝ} (h : Zc γ' = Zc γ) :
    ParityCore γ' ↔ ParityCore γ := by
  rw [parityCore_iff_set, parityCore_iff_set, h]

/-- **The parity core is translation invariant.**

`Work.Drive.goodC_translate` shows `GoodC (fun t => γ t + c) = GoodC γ`, hence
`Zc (fun t => γ t + c) = Zc γ` (`Work.Drive.Zc_translate`).  Since `ParityCore γ` is a statement
about the *set* `Zc γ` alone, it is unchanged by translating `γ`.

This matters for the order-theory route: the capping of the configuration Möbius strip uses polar
coordinates about the origin and therefore assumes the curve avoids the origin (otherwise the strip
meets the axis `{0} × S¹ × {0}` of the configuration space).  Translation invariance is what allows
that hypothesis to be arranged.

Proof note: `rw [ParityCore, ParityCore, Zc_translate γ c]` fails ("motive is not type correct"),
because `Zc` occurs inside `Subtype` and inside the membership proof `neg_mem_Zc`.  The intended route
is a general transport lemma `parityCore_congr : Zc γ' = Zc γ → (ParityCore γ' ↔ ParityCore γ)`,
moving `b` along the subtype equality (proof irrelevance handles the `neg_mem_Zc` arguments), which is
then applied to `Zc_translate γ c`. -/
theorem parityCore_translate (γ : Circle → ℝ × ℝ) (c : ℝ × ℝ) :
    ParityCore (fun t => γ t + c) ↔ ParityCore γ :=
  parityCore_congr (Zc_translate γ c)

end Work.Drive

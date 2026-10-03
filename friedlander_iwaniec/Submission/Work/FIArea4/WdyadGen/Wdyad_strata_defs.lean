import Mathlib
import Submission.Work.FIArea4.WdyadGenDefs
import Submission.Work.FIArea4.Wdyad_units

/-!
# Elementary vocabulary for the stratum-energy bound `Wdyad_strata_energy`

This module collects the notation used by `Wdyad_strata_energy`:

* `TZone d₀ β r s` — the class sum `Σ_{a<d₀} β a d₀ · Mentry d₀ a r s` over a *single* modulus;
* `WboxI R slo shi dlo dhi β` — the dual dyadic box form `Σ_{R<r≤2R} Σ_{slo<s≤shi} ‖TZbox dlo dhi β r s‖²`;
* `rowE β d` — the energy `Σ_{a<d} ‖β a d‖²` of one modulus row;
* `stratEn D e γ` — the total energy `Σ_{D/e < d' ≤ 2D/e} Σ_{a'<d'} ‖gamE γ e a' d'‖²` of the
  `gcd = e` stratum of `γ`.
-/

namespace Work.FIArea4.WdyadGen

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The class sum over a single modulus `d₀`. -/
def TZone (d₀ : ℕ) (β : ℕ → ℕ → ℂ) (r s : ℕ) : ℂ :=
  ∑ a ∈ Finset.range d₀, β a d₀ * Work.FIArea4.Mentry d₀ a r s

/-- The dual form over an arbitrary pair of index boxes. -/
def WboxI (R slo shi dlo dhi : ℕ) (β : ℕ → ℕ → ℂ) : ℝ :=
  ∑ r ∈ Finset.Ioc R (2 * R), ∑ s ∈ Finset.Ioc slo shi,
    Complex.normSq (Work.FIArea4.TZbox dlo dhi β r s)

/-- The energy of one modulus row. -/
def rowE (β : ℕ → ℕ → ℂ) (d : ℕ) : ℝ :=
  ∑ a ∈ Finset.range d, Complex.normSq (β a d)

/-- The energy of the `gcd = e` stratum of `γ` (over the modulus window `(D, 2D]`). -/
def stratEn (D e : ℕ) (γ : ℕ → ℕ → ℂ) : ℝ :=
  ∑ d' ∈ Finset.Ioc (D / e) (2 * D / e), ∑ a' ∈ Finset.range d',
    Complex.normSq (Work.FIArea4.gamE γ e a' d')

/-- `Wdyad` is the box form at the dyadic window. -/
lemma Wdyad_eq_WboxI (D R S : ℕ) (β : ℕ → ℕ → ℂ) :
    Work.FIArea4.Wdyad D R S β = WboxI R S (2 * S) D (2 * D) β := rfl

/-- `WE` is the sum of the row energies. -/
lemma WE_eq_sum_rowE (D : ℕ) (β : ℕ → ℕ → ℂ) :
    Work.FIArea4.WE D β = ∑ d ∈ Finset.Ioc D (2 * D), rowE β d := rfl

lemma WboxI_nonneg (R slo shi dlo dhi : ℕ) (β : ℕ → ℕ → ℂ) :
    0 ≤ WboxI R slo shi dlo dhi β :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))

lemma rowE_nonneg (β : ℕ → ℕ → ℂ) (d : ℕ) : 0 ≤ rowE β d :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

lemma stratEn_nonneg (D e : ℕ) (γ : ℕ → ℕ → ℂ) : 0 ≤ stratEn D e γ :=
  Finset.sum_nonneg (fun _ _ => rowE_nonneg _ _)

/-- Monotonicity of `WboxI` in the `s`-window (the summands are nonnegative). -/
lemma WboxI_mono_s (R slo shi slo' shi' dlo dhi : ℕ) (β : ℕ → ℕ → ℂ)
    (hlo : slo ≤ slo') (hhi : shi' ≤ shi) :
    WboxI R slo' shi' dlo dhi β ≤ WboxI R slo shi dlo dhi β := by
  refine Finset.sum_le_sum (fun r _ => ?_)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro s hs
    simp only [Finset.mem_Ioc] at hs ⊢
    exact ⟨lt_of_le_of_lt hlo hs.1, le_trans hs.2 hhi⟩
  · intro s _ _; exact Complex.normSq_nonneg _

/-- Splitting a `TZbox` sum over a modulus window. -/
lemma TZbox_add (lo hi hi' : ℕ) (β : ℕ → ℕ → ℂ) (hl : lo ≤ hi) (h : hi ≤ hi') (r s : ℕ) :
    Work.FIArea4.TZbox lo hi' β r s
      = Work.FIArea4.TZbox lo hi β r s + Work.FIArea4.TZbox hi hi' β r s := by
  simp only [Work.FIArea4.TZbox]
  rw [← Finset.sum_union]
  · congr 1
    exact (Finset.Ioc_union_Ioc_eq_Ioc hl h).symm
  · rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Ioc] at hx hy
    exact absurd hy.1 (not_lt.mpr hx.2)

end

end Work.FIArea4.WdyadGen

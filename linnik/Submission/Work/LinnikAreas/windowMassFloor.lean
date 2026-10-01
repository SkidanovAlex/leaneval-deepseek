import Mathlib
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.sum_mul_exp_neg_le_of_count
import Submission.Work.LinnikAreas.pairCountHeight_dom
import Submission.Work.LinnikAreas.siegelRestHigh

namespace Work.LinnikAreas

/-- **Per-height-window Abel summation with a repulsion floor.**  Let `S` be a finite set of
zero-pairs of level `q > 1`, all of height `|Im ρ|·𝓛 ≤ H·𝓛`, none of them the exceptional pair, and
suppose the `λ₁`-free log-free count at height `H` is available in the form
`pairCountHeight χ₁ β₁ t (H·𝓛) ≤ C₂·e^{(5/2)t}·H^{3/2}` for `0 < t ≤ 𝓛`.  If moreover every member of
`S` has `λ(ρ) ≥ Λ` for a *positive* `Λ`, then
`Σ_{(χ,ρ) ∈ S} mult(ρ)·e^{-(49/10)λ(ρ)} ≤ C₂·H^{3/2}·e^{5/2}·e^{-(12/5)Λ}/(1 - e^{-(12/5)})`.

Proof: `Work.LinnikAreas.sum_mul_exp_neg_le_of_count` with `S`, `m = mult`, `lam = λ`,
`a₀ = 49/10`, `Λ`, `L = 𝓛`, `D = C₂`, `lam₁ = H^{3/2}`, `c = 5/2`; the counting hypothesis is
`Work.LinnikAreas.pairCountHeight_dom` composed with `hcnt`, and `λ(z) ≤ 𝓛` for zeros follows from
`Work.LinnikAreas.zeroMult_re_pos` (in `Submission/Work/LinnikAreas/siegelRestHigh.lean`). -/
lemma windowMassFloor {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    {C₂ H Λ : ℝ} (hC₂ : 0 < C₂) (hH : 0 < H) (hΛ : 0 < Λ)
    (hcnt : ∀ t : ℝ, 0 < t → t ≤ Real.log (q : ℝ) →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ C₂ * Real.exp ((5 / 2) * t) * H ^ (3 / 2 : ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁))
    (him : ∀ z ∈ S, |z.2.im| * Real.log (q : ℝ) ≤ H * Real.log (q : ℝ))
    (hfloor : ∀ z ∈ S, Λ ≤ Work.LinnikContract.lamOf q z.2) :
    (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
      ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp (5 / 2) * Real.exp (-(12 / 5) * Λ)
          / (1 - Real.exp (-(12 / 5))) := by
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  -- every zero of the window lies in the strip `λ(ρ) ≤ 𝓛`
  have hlamL : ∀ z ∈ S, Work.LinnikContract.lamOf q z.2 ≤ Real.log (q : ℝ) := by
    intro z hz
    have h1 : 0 < z.2.re := zeroMult_re_pos z.1 (hzm z hz)
    rw [Work.LinnikContract.lamOf]
    calc (1 - z.2.re) * Real.log (q : ℝ) ≤ 1 * Real.log (q : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) hlog.le
      _ = Real.log (q : ℝ) := by ring
  -- the counting hypothesis of the layer-cake theorem, at every cut-off `t ∈ [Λ, 𝓛]`
  have hcount : ∀ t : ℝ, Λ ≤ t → t ≤ Real.log (q : ℝ) →
      (∑ z ∈ S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t),
          (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
        ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp ((5 / 2) * t) := by
    intro t htΛ htL
    have htpos : 0 < t := lt_of_lt_of_le hΛ htΛ
    have hdom := pairCountHeight_dom hq χ₁ β₁
      (S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t))
      (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
      (fun z hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => him z (Finset.mem_filter.mp hz).1)
      (fun z hz => hexc z (Finset.mem_filter.mp hz).1)
    have hc := hcnt t htpos htL
    calc (∑ z ∈ S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t),
            (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
        ≤ Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ)) := hdom
      _ ≤ C₂ * Real.exp ((5 / 2) * t) * H ^ (3 / 2 : ℝ) := hc
      _ = C₂ * H ^ (3 / 2 : ℝ) * Real.exp ((5 / 2) * t) := by ring
  have hmain := sum_mul_exp_neg_le_of_count (S := S)
    (m := fun z : DirichletCharacter ℂ q × ℂ => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
    (lam := fun z : DirichletCharacter ℂ q × ℂ => Work.LinnikContract.lamOf q z.2)
    (a₀ := 49 / 10) (Λ := Λ) (L := Real.log (q : ℝ)) (D := C₂)
    (lam₁ := H ^ (3 / 2 : ℝ)) (c := 5 / 2)
    (by norm_num) (by norm_num) (by norm_num) hC₂ hΛ (Real.rpow_pos_of_pos hH _)
    (fun z _ => Nat.cast_nonneg _) (fun z hz => hfloor z hz) hlamL hcount
  have hnum : (5 / 2 - 49 / 10 : ℝ) = -(12 / 5) := by norm_num
  rw [hnum] at hmain
  exact hmain

end Work.LinnikAreas

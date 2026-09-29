import Mathlib
import Submission.Work.TMC16Core.Assembly.Branch
import Submission.Work.TMC16Core.Trig.shift_block
import Submission.Work.TMC16Core.CF.cf_data_bridge
import Submission.Work.TMC16Core.Core.uni_res5
import Submission.Work.TMC16Core.Core.coll_res
import Submission.Work.TMC16Core.Core.Uniform_equiv
import Submission.Work.TMC16Core.Assembly.uni_res_ell_le
import Submission.Work.TMC16Core.Assembly.uni_res_rate

namespace Work.TMC16Core.Assembly

open Work.TMC16Core
open Work.TMC16Core.Core

noncomputable section

/-! ## Monotonicity of `Uniform` in the rate -/

theorem Uniform_mono {ι : Type*} [Fintype ι] [DecidableEq ι] {ε ε' : ℝ} (h : ε ≤ ε')
    {z : ι → ℝ} (hz : Uniform ε z) : Uniform ε' z := by
  rw [Uniform] at hz ⊢
  refine ⟨hz.1, fun j x hx => ?_⟩
  refine lt_of_lt_of_le (hz.2 j x hx) (Real.exp_le_exp.mpr ?_)
  have hcard : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨j⟩
  nlinarith

/-! ## The bijection between the two presentations of the resonant windows

`I1r qn ∪ I2r qn ℓ` (site coordinates of `Assembly.Branch`) is the image of
`J1resG (5 qn / 8) ∪ J2resG qn (5 qn / 8) ℓ` (phase-index coordinates of `Core.windows`)
under the shift `j ↦ j - (qn - 1)`. -/

theorem image_shift_eq (qn ℓ : ℕ) :
    (J1resG (5 * qn / 8) ∪ J2resG qn (5 * qn / 8) ℓ).image (fun j => j - ((qn : ℤ) - 1))
      = I1r qn ∪ I2r qn ℓ := by
  rw [Finset.image_union]
  congr 1
  · ext x
    simp only [J1resG, I1r, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
      omega
    · intro hx
      exact ⟨x + ((qn : ℤ) - 1), ⟨by omega, by omega⟩, by ring⟩
  · ext x
    simp only [J2resG, I2r, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
      omega
    · intro hx
      exact ⟨x + ((qn : ℤ) - 1), ⟨by omega, by omega⟩, by ring⟩

/-- The bijection `k ↦ k + (qn - 1)` between the two index sets of the resonant windows. -/
def uniResEquiv (qn ℓ : ℕ) :
    {k : ℤ // k ∈ I1r qn ∪ I2r qn ℓ} ≃
      {j : ℤ // j ∈ J1resG (5 * qn / 8) ∪ J2resG qn (5 * qn / 8) ℓ} where
  toFun k := ⟨(k : ℤ) + ((qn : ℤ) - 1), by
    have hmem : (k : ℤ) ∈ (J1resG (5 * qn / 8) ∪ J2resG qn (5 * qn / 8) ℓ).image
        (fun j => j - ((qn : ℤ) - 1)) := by
      rw [image_shift_eq]
      exact k.property
    obtain ⟨a, ha, har⟩ := Finset.mem_image.mp hmem
    have hval : a = (k : ℤ) + ((qn : ℤ) - 1) := by omega
    rwa [hval] at ha⟩
  invFun j := ⟨(j : ℤ) - ((qn : ℤ) - 1), by
    have hmem : ((j : ℤ) - ((qn : ℤ) - 1)) ∈ (J1resG (5 * qn / 8)
        ∪ J2resG qn (5 * qn / 8) ℓ).image (fun j => j - ((qn : ℤ) - 1)) :=
      Finset.mem_image.mpr ⟨(j : ℤ), j.property, rfl⟩
    rwa [image_shift_eq] at hmem⟩
  left_inv k := by
    ext
    simp only
    ring
  right_inv j := by
    ext
    simp only
    ring

/-- The same bijection in the reverse direction (`j ↦ j - (qn - 1)`). -/
def uniResEquivSymm (qn ℓ : ℕ) :
    {j : ℤ // j ∈ J1resG (5 * qn / 8) ∪ J2resG qn (5 * qn / 8) ℓ} ≃
      {k : ℤ // k ∈ I1r qn ∪ I2r qn ℓ} where
  toFun j := ⟨(j : ℤ) - ((qn : ℤ) - 1), by
    have hmem : ((j : ℤ) - ((qn : ℤ) - 1)) ∈ (J1resG (5 * qn / 8)
        ∪ J2resG qn (5 * qn / 8) ℓ).image (fun j => j - ((qn : ℤ) - 1)) :=
      Finset.mem_image.mpr ⟨(j : ℤ), j.property, rfl⟩
    rwa [image_shift_eq] at hmem⟩
  invFun k := ⟨(k : ℤ) + ((qn : ℤ) - 1), by
    have hmem : (k : ℤ) ∈ (J1resG (5 * qn / 8) ∪ J2resG qn (5 * qn / 8) ℓ).image
        (fun j => j - ((qn : ℤ) - 1)) := by
      rw [image_shift_eq]
      exact k.property
    obtain ⟨a, ha, har⟩ := Finset.mem_image.mp hmem
    have hval : a = (k : ℤ) + ((qn : ℤ) - 1) := by omega
    rwa [hval] at ha⟩
  left_inv j := by
    ext
    simp only
    ring
  right_inv k := by
    ext
    simp only
    ring

end

end Work.TMC16Core.Assembly

namespace Work.TMC16Core.Assembly

open Work.TMC16Core
open Work.TMC16Core.Core

noncomputable section

/-! ## The main theorem -/

theorem uni_res {α b₀ lam L : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {θ cθ : ℝ}
    (hα : Irrational α) (hb₀ : 0 < b₀) (hDioph : Work.TMC16Core.DiophBelow α b₀)
    (hL : L = Real.log lam) (hlam : 1 < lam) (hLb : 16 * b₀ / 9 < L)
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) →
      Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    (hcθ : 0 < cθ) (hcθ1 : cθ ≤ 1 / 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ ℓ : ℕ, 1 ≤ ℓ →
      (ℓ : ℝ) ≤ Real.rpow (q (n + 1) : ℝ) (8 / 9) / (q n : ℝ) →
      (∀ j : ℤ, |j| ≤ 6 * (q (n + 1) : ℤ) + 6 * (q n : ℤ) + 4 →
        cθ ≤ Work.TMC16Core.fracDist (2 * θ + (j : ℝ) * α)) →
      Work.TMC16Core.Uniform (9 * L / 32 - ε)
        (fun j : {j : ℤ // j ∈ Work.TMC16Core.Assembly.I1r (q n)
            ∪ Work.TMC16Core.Assembly.I2r (q n) ℓ} =>
          θ + (((j : ℤ) : ℝ) + ((q n : ℝ) - 1)) * α) := by
  have hδpos : 0 < 9 * L / 32 - b₀ / 2 := by linarith [hLb]
  -- the rate: `uni_res_rate` supplies the threshold and the estimate
  obtain ⟨Q, hQpos, hQbound⟩ := uni_res_rate hb₀ hcθ hLb
  obtain ⟨Qn, hQn⟩ := exists_nat_ge Q
  -- the Diophantine threshold
  have hDioph' : ∃ K : ℕ, ∀ k ≥ K, Real.exp (-(b₀ * (k : ℝ))) ≤
      Work.TMC16Core.fracDist ((k : ℝ) * α) := by
    have h := hDioph
    rw [Work.TMC16Core.DiophBelow, Filter.eventually_atTop] at h
    exact h
  obtain ⟨K, hK⟩ := hDioph'
  refine ⟨(9 * L / 32 - b₀ / 2) / 2, ?_, 2 + (Qn + 1) + (10 ^ 9 + 1) + (K + 1), ?_⟩
  · -- positivity of the rate slack
    linarith [hδpos]
  intro n hn ℓ hℓ hℓle hθt
  have hN2 : 2 ≤ n := by omega
  have hQn1 : Qn + 1 ≤ n := by omega
  have h9 : 10 ^ 9 + 1 ≤ n := by omega
  have hK1 : K + 1 ≤ n := by omega
  -- `q m ≥ m + 1`
  have hqge : ∀ m : ℕ, m + 1 ≤ q m := by
    intro m
    induction m with
    | zero => have := hqpos 0; omega
    | succ k ih =>
      have h1 : q k + 1 ≤ q (k + 1) := by
        show q k + 1 ≤ q k.succ
        have := hmono (Nat.lt_succ_self k)
        omega
      have h2 : k + 1 ≤ q k := ih
      show k + 1 + 1 ≤ q (k + 1)
      omega
  have hqn_ge : Q ≤ (q n : ℝ) := by
    have h1 : (Qn : ℝ) + 1 ≤ (q n : ℝ) := by
      have h2 : Qn + 1 ≤ q n := by
        have h3 := hqge n
        omega
      exact_mod_cast h2
    have h2 : Q ≤ (Qn : ℝ) := hQn
    linarith
  have hP9 : 10 ^ 9 ≤ q (n + 1) := by
    have h2 := hqge (n + 1)
    omega
  have hKq : K ≤ q n := by
    have h2 := hqge n
    omega
  have hqposn : 0 < q n := hqpos n
  -- the continued-fraction inequality `10 ℓ q n ≤ q (n+1)`
  have hℓb : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ) :=
    uni_res_ell_le hℓ hP9 hqposn hℓle
  have hℓqn : (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ) := by
    have h0 : (0 : ℤ) ≤ (ℓ : ℤ) * (q n : ℤ) := by positivity
    linarith [hℓb]
  have hPn : (q n : ℤ) ≤ (q (n + 1) : ℤ) := by
    have h := hmono (Nat.lt_succ_self n)
    exact_mod_cast h.le
  -- the `θ`-hypothesis in the form required by `uni_res5`
  have hθ' : ∀ k : ℤ, |k| ≤ 4 * ((ℓ : ℤ) + 2) * (q n : ℤ) →
      cθ ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α) := by
    intro k hk
    apply hθt
    have hkey : 4 * ((ℓ : ℤ) + 2) * (q n : ℤ) ≤
        6 * (q (n + 1) : ℤ) + 6 * (q n : ℤ) + 4 := by
      nlinarith [hℓqn, hPn]
    linarith [hk, hkey]
  -- the geometric growth `q (n+1) ≤ e^{b₀ q n}`
  have hβ : (q (n + 1) : ℝ) ≤ Real.exp (b₀ * (q n : ℝ)) := by
    have h1 : Real.exp (-(b₀ * (q n : ℝ))) ≤
        Work.TMC16Core.fracDist ((q n : ℝ) * α) := hK (q n) hKq
    rw [← hΔeq n] at h1
    have h2 : Δ n < 1 / (q (n + 1) : ℝ) := hΔup n
    have hPpos : (0 : ℝ) < (q (n + 1) : ℝ) := by
      have := hqpos (n + 1)
      exact_mod_cast this
    have h3 : Real.exp (-(b₀ * (q n : ℝ))) < 1 / (q (n + 1) : ℝ) := lt_of_le_of_lt h1 h2
    have h4 : Real.exp (-(b₀ * (q n : ℝ))) * (q (n + 1) : ℝ) < 1 :=
      (lt_div_iff₀ hPpos).mp h3
    have hepos : 0 < Real.exp (-(b₀ * (q n : ℝ))) := Real.exp_pos _
    have h5 : (q (n + 1) : ℝ) < (Real.exp (-(b₀ * (q n : ℝ))))⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ hepos]
      linarith [h4]
    have h6 : (Real.exp (-(b₀ * (q n : ℝ))))⁻¹ = Real.exp (b₀ * (q n : ℝ)) := by
      rw [← Real.exp_neg]
      ring_nf
    rw [h6] at h5
    exact h5.le
  -- the collision estimate
  have hcoll : ∀ j ∈ J1resG (5 * q n / 8) ∪ J2resG (q n) (5 * q n / 8) ℓ,
      -b₀ * (q n : ℝ) - 10 ≤
        ∑ i ∈ (J1resG (5 * q n / 8) ∪ J2resG (q n) (5 * q n / 8) ℓ).filter
            (fun i => i ≠ j ∧ (q n : ℤ) ∣ (i - j)),
          Real.log |Real.sin (Real.pi * (((i - j : ℤ)) : ℝ) * α)| :=
    coll_res (α := α) (β := b₀) (q := q) (n := n) (h := 5 * q n / 8) (ℓ := ℓ)
      (le_of_lt hb₀) (by omega) hℓ (by omega) le_rfl hℓb
      (by rw [← hΔeq n]; exact hΔlo n) (by rw [← hΔeq n]; exact (hΔup n).le) hβ
  -- `uni_res5`
  have huni5 : Uniform (b₀ / 2 + b₀ / (4 * (q n : ℝ) - 2)
      + 2 * Real.log (1 / cθ) / (q n : ℝ)
      + 200 * Real.log (q n : ℝ) / (q n : ℝ) + 200 / (q n : ℝ))
      (fun j : {j : ℤ // j ∈ J1resG (5 * q n / 8) ∪ J2resG (q n) (5 * q n / 8) ℓ} =>
        θ + (j : ℝ) * α) :=
    uni_res5 (α := α) (β := b₀) (q := q) (Δ := Δ) (n := n) (h := 5 * q n / 8) (ℓ := ℓ)
      (θ := θ) (c := cθ) hqpos hmono hΔpos hΔeq hΔup hΔlo hbest (le_of_lt hb₀) hN2 hℓ
      (by omega) le_rfl hℓb hβ hcθ hθ' hcoll
  -- the rate comparison
  have hrate : b₀ / 2 + b₀ / (4 * (q n : ℝ) - 2) + 2 * Real.log (1 / cθ) / (q n : ℝ)
      + 200 * Real.log (q n : ℝ) / (q n : ℝ) + 200 / (q n : ℝ)
      ≤ 9 * L / 32 - (9 * L / 32 - b₀ / 2) / 2 :=
    hQbound (q n) hqn_ge
  -- transfer to the target family
  refine Core.Uniform_equiv (uniResEquivSymm (q n) ℓ) ?_ (Uniform_mono hrate huni5)
  intro j
  have hval : (((uniResEquivSymm (q n) ℓ j : ℤ)) : ℝ) = (j : ℝ) - ((q n : ℝ) - 1) := by
    have h : ((uniResEquivSymm (q n) ℓ j : ℤ)) = (j : ℤ) - ((q n : ℤ) - 1) := rfl
    rw [h]
    push_cast
    ring
  simp only [hval]
  ring


end

end Work.TMC16Core.Assembly

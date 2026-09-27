import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.tendsto_of_mem_V
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLProd.borelOrbitImage
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLComp.exists_isCompact_image

/-!
# Uniform injectivity of `x ↦ g • x` on compact subsets of `X₃`

The fourth conjunct of the frozen component `P_X3` (`Submission/Work/EKLContract/Defs.lean`):
for every compact `K ⊆ X₃ = SL₃(ℝ)/SL₃(ℤ)` there is `δ > 0` such that on `K` the displacement
neighbourhood `V δ` of the identity acts injectively:

`∀ x ∈ K, ∀ g h ∈ V δ, g • x = h • x → g = h`.

(No metric on `X₃` is involved: `V δ = {g | ∀ i j, |g i j - 1 i j| < δ}`.)

## The argument

The group `Γ₃ = SL₃(ℤ)` is discrete (indeed `Γ₃ ∩ V (1/2) = {1}`, because all entries of a
matrix in `Γ₃` are integers and `V (1/2)` forces every entry within `1/2` of the corresponding
entry of the identity).  Hence the stabiliser of `x = pΓ₃`, which is the conjugate `pΓ₃p⁻¹`, is
uniformly far from `1` *as long as `p` stays in a fixed compact set*, and every compact
`K ⊆ X₃` lifts to a compact `C ⊆ SL₃(ℝ)` with `K ⊆ mkX '' C`
(`Work.EKLComp.exists_isCompact_image`).

Suppose the conclusion fails for a compact `K`.  Then for every `n` there are `x n ∈ K`,
`g n, h n ∈ V (1/(n+1))` with `g n • x n = h n • x n` and `g n ≠ h n`.  Pick `p n ∈ C` with
`mkX (p n) = x n` and pass to a convergent subsequence `p (φ n) → a`.  Then

`e n := (h (φ n))⁻¹ * g (φ n) → 1` and `c n := (p (φ n))⁻¹ * e n * p (φ n) → a⁻¹ * 1 * a = 1`

by continuity of the group operations in `SL₃(ℝ)`.  Since `e n • x n = x n` we have
`mkX (g n * p n) = mkX (h n * p n)`, and `QuotientGroup.eq` gives
`c n = ((g n * p n)⁻¹ * (h n * p n))⁻¹ ∈ Γ₃`; also `c n ≠ 1` because `c n = 1` forces
`e n = 1`, i.e. `g n = h n`.  Finally `c n ∈ Γ₃` and `c n → 1` give `c n ∈ V (1/2)` eventually,
hence `c n = 1` by discreteness — a contradiction.

The only topological input is `Work.EKLC6Core.tendsto_of_mem_V` (`g n ∈ V (u n)`, `u n → 0`
forces `g n → 1`).
-/

namespace Work.EKLC6Core

open Work.EKLContract Filter Topology

/-- **Discreteness of `Γ₃` at the identity, in entrywise form**: the only element of
`Γ₃ = SL₃(ℤ)` whose entries are all within `1/2` of the corresponding entries of the identity
matrix is `1` itself.  (Every entry of a matrix of `Γ₃` is an integer, and the only integer
within distance `1/2` of `1` resp. `0` is `1` resp. `0`.) -/
theorem eq_one_of_mem_Γ3_mem_V_half : ∀ γ : SL3, γ ∈ Γ3 → γ ∈ V ((1:ℝ)/2) → γ = 1 := by
  intro γ hγ hVγ
  refine Subtype.ext (Matrix.ext ?_)
  intro i j
  obtain ⟨k, hk⟩ := Work.EKLContract.Lemmas.Γ3_integral_entries γ hγ i j
  have hb : |(k : ℝ) - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < (1:ℝ)/2 := by
    have h := hVγ i j
    rw [hk] at h
    exact h
  rw [Matrix.one_apply] at hb
  rw [show ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) = (1 : Matrix (Fin 3) (Fin 3) ℝ)
      from rfl, Matrix.one_apply]
  by_cases hij : i = j
  · rw [if_pos hij] at hb ⊢
    have h2 : (0:ℝ) < (k:ℝ) := by have := abs_lt.mp hb; linarith [this.1]
    have h3 : (k:ℝ) < 2 := by have := abs_lt.mp hb; linarith [this.2]
    have hk1 : k = 1 := by
      have h2' : (0:ℤ) < k := by exact_mod_cast h2
      have h3' : k < 2 := by exact_mod_cast h3
      omega
    rw [hk, hk1]
    norm_num
  · rw [if_neg hij] at hb ⊢
    have h2 : (-1:ℝ) < (k:ℝ) := by have := abs_lt.mp hb; linarith [this.1]
    have h3 : (k:ℝ) < 1 := by have := abs_lt.mp hb; linarith [this.2]
    have hk0 : k = 0 := by
      have h2' : (-1:ℤ) < k := by exact_mod_cast h2
      have h3' : k < 1 := by exact_mod_cast h3
      omega
    rw [hk, hk0]
    norm_num

theorem uniform_injective_V_X3 : ∀ K : Set Work.EKLContract.X3, IsCompact K →
    ∃ δ > 0, ∀ x ∈ K, ∀ g ∈ Work.EKLContract.V δ, ∀ h ∈ Work.EKLContract.V δ,
      g • x = h • x → g = h := by
  intro K hK
  -- the compact lift `K ⊆ mkX '' C`
  obtain ⟨C, hC, hKC⟩ := Work.EKLComp.exists_isCompact_image K hK
  by_contra hcon
  push Not at hcon
  -- a bad sequence: `x n ∈ K`, `g n, h n ∈ V (1/(n+1))`, `g n • x n = h n • x n`, `g n ≠ h n`
  choose x hxK g hgV h hhV hgh hne using
    fun n : ℕ => hcon (1/((n:ℝ)+1)) (by positivity)
  choose p hpC hpx using fun n => hKC (hxK n)
  -- pass to a convergent subsequence of the lifts
  obtain ⟨aa, _, φ, hφmono, hφtend⟩ := hC.tendsto_subseq hpC
  -- `h (φ n) → 1` and `g (φ n) → 1`, since both lie in `V (1/(φ n + 1))`
  have hlim : Tendsto (fun n : ℕ => (1:ℝ)/(((φ n : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφmono.tendsto_atTop
  have hlimh : Tendsto (fun n => h (φ n)) atTop (𝓝 (1:SL3)) :=
    tendsto_of_mem_V hlim (fun n => hhV (φ n))
  have hlimg : Tendsto (fun n => g (φ n)) atTop (𝓝 (1:SL3)) :=
    tendsto_of_mem_V hlim (fun n => hgV (φ n))
  -- the conjugate displacement `c n`
  have hee : Tendsto (fun n => (h (φ n))⁻¹ * g (φ n)) atTop (𝓝 (1:SL3)) := by
    have := hlimh.inv.mul hlimg
    simpa using this
  have hpp : Tendsto (fun n => p (φ n)) atTop (𝓝 aa) := hφtend
  have hcc : Tendsto (fun n => (p (φ n))⁻¹ * ((h (φ n))⁻¹ * g (φ n)) * p (φ n)) atTop
      (𝓝 (1:SL3)) := by
    have h1 : Tendsto (fun n => (p (φ n))⁻¹ * ((h (φ n))⁻¹ * g (φ n))) atTop
        (𝓝 (aa⁻¹ * 1)) := hpp.inv.mul hee
    have h2 := h1.mul hpp
    simpa using h2
  -- `c n` lies in the lattice `Γ₃`
  have hmem : ∀ n, (p (φ n))⁻¹ * ((h (φ n))⁻¹ * g (φ n)) * p (φ n) ∈ Γ3 := by
    intro n
    have h1 : mkX (g (φ n) * p (φ n)) = mkX (h (φ n) * p (φ n)) := by
      rw [Work.EKLContract.Lemmas.mkX_mul, Work.EKLContract.Lemmas.mkX_mul, hpx (φ n)]
      exact hgh (φ n)
    have h2 : ((g (φ n) * p (φ n))⁻¹ * (h (φ n) * p (φ n))) ∈ Γ3 :=
      QuotientGroup.eq.mp (show QuotientGroup.mk (g (φ n) * p (φ n))
        = QuotientGroup.mk (h (φ n) * p (φ n)) from h1)
    have h3 : ((g (φ n) * p (φ n))⁻¹ * (h (φ n) * p (φ n)))⁻¹ ∈ Γ3 := Γ3.inv_mem h2
    have heq : ((g (φ n) * p (φ n))⁻¹ * (h (φ n) * p (φ n)))⁻¹
        = (p (φ n))⁻¹ * ((h (φ n))⁻¹ * g (φ n)) * p (φ n) := by group
    rw [heq] at h3
    exact h3
  -- `c n ≠ 1`, since `c n = 1` forces `g (φ n) = h (φ n)`
  have hne' : ∀ n, (p (φ n))⁻¹ * ((h (φ n))⁻¹ * g (φ n)) * p (φ n) ≠ 1 := by
    intro n h1
    refine hne (φ n) ?_
    have h2 : (h (φ n))⁻¹ * g (φ n) = 1 := by
      have := congrArg (fun z => p (φ n) * z * (p (φ n))⁻¹) h1
      simpa [mul_assoc] using this
    have h3 : g (φ n) = h (φ n) * ((h (φ n))⁻¹ * g (φ n)) := by group
    rw [h3, h2, mul_one]
  -- `c n → 1` and `V (1/2)` is a neighbourhood of `1`, so eventually `c n ∈ V (1/2) ∩ Γ₃ = {1}`
  have hVmem : V ((1:ℝ)/2) ∈ 𝓝 (1 : SL3) := by
    have h := Work.EKLContract.Lemmas.V_open_one ((1:ℝ)/2) (by norm_num)
    exact h.1.mem_nhds h.2
  have hev : ∀ᶠ n in atTop,
      (p (φ n))⁻¹ * ((h (φ n))⁻¹ * g (φ n)) * p (φ n) ∈ V ((1:ℝ)/2) :=
    hcc.eventually hVmem
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  exact hne' N (eq_one_of_mem_Γ3_mem_V_half _ (hmem N) (hN N le_rfl))

end Work.EKLC6Core

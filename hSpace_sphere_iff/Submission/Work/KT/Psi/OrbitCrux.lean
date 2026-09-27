import Mathlib
import Submission.Work.KT.Psi.OrbitBasic
import Submission.Work.KT.Psi.OrbitFi
import Submission.Work.KT.Psi.OrbitFacts

namespace Work.KT.Psi

open Finset

variable {M : Type} [Ring M] [Algebra ℂ M]

/-- `F * E * F = k⁻¹ • F`, where `E = orbitSpec lam g k`.  Only the `j = 0` term of the
geometric sum survives. -/
lemma orbitCrux_FEF (k : ℕ) (hk : 0 < k) (F g : M) (hF : F * F = F) (hg : g ^ k = 1)
    (horth : ∀ i j : ℕ, i < k → j < k → i ≠ j →
      (g ^ i * F * g ^ (k - i)) * (g ^ j * F * g ^ (k - j)) = 0)
    (lam : ℂ) (hlam : lam ^ k = 1) :
    F * orbitSpec lam g k * F = ((k : ℂ)⁻¹) • F := by
  have hinner : ∀ j ∈ Finset.range k,
      F * ((lam⁻¹) ^ j • (Fi g F k j * g ^ j)) = (lam⁻¹) ^ j • ((F * Fi g F k j) * g ^ j) := by
    intro j hj
    rw [mul_smul_comm, mul_assoc]
  have hterm : ∀ j ∈ Finset.range k, j ≠ 0 →
      (lam⁻¹) ^ j • ((F * Fi g F k j) * g ^ j) = 0 := by
    intro j hj hne
    have hzero : F * Fi g F k j = 0 := by
      have h : Fi g F k 0 * Fi g F k j = 0 :=
        Fi_mul_orth hk (Finset.mem_range.mp hj) (Ne.symm hne) horth
      simpa only [Fi_zero hg] using h
    rw [hzero, zero_mul, smul_zero]
  have hS : F * (∑ j ∈ Finset.range k, (lam⁻¹) ^ j • (Fi g F k j * g ^ j)) = F := by
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl hinner]
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hk)]
    · simp [Fi_zero hg, hF]
    · intro j hj hne
      exact hterm j hj hne
  rw [mul_assoc, orbitSpec_mul_eq_sum k F g hg lam, mul_smul_comm, hS]

/-- `E * F * E = k⁻¹ • (O * E)`, where `E = orbitSpec lam g k` and `O = orbSum g F k`:
the `λ`-twists cancel against `g^j E = λ^j E`. -/
lemma orbitCrux_EFE (k : ℕ) (hk : 0 < k) (F g : M) (hF : F * F = F) (hg : g ^ k = 1)
    (horth : ∀ i j : ℕ, i < k → j < k → i ≠ j →
      (g ^ i * F * g ^ (k - i)) * (g ^ j * F * g ^ (k - j)) = 0)
    (lam : ℂ) (hlam : lam ^ k = 1) :
    orbitSpec lam g k * F * orbitSpec lam g k =
      ((k : ℂ)⁻¹) • (orbSum g F k * orbitSpec lam g k) := by
  have hq : qg lam g ^ k = 1 := qg_pow_eq_one hg hlam
  have hlam_ne : lam ≠ 0 := ne_zero_of_pow_eq_one hk hlam
  have hlaminv : ∀ j, (lam⁻¹) ^ j * lam ^ j = (1 : ℂ) := by
    intro j
    rw [← mul_pow, inv_mul_cancel₀ hlam_ne, one_pow]
  have hgE : ∀ j, g ^ j * orbitSpec lam g k = (lam ^ j) • orbitSpec lam g k := by
    intro j
    rw [g_pow_mul_orbitSpec hk hlam hq j, ← Algebra.smul_def]
  have hterm : ∀ j ∈ Finset.range k,
      ((lam⁻¹) ^ j • (Fi g F k j * g ^ j)) * orbitSpec lam g k
        = Fi g F k j * orbitSpec lam g k := by
    intro j hj
    rw [smul_mul_assoc, mul_assoc, hgE j, mul_smul_comm, smul_smul, hlaminv j, one_smul]
  rw [orbitSpec_mul_eq_sum k F g hg lam, smul_mul_assoc]
  congr 1
  rw [Finset.sum_mul, Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← orbSum_eq_sum_Fi]

/-- The two "orbit ♢ spectral projector" identities: with `O = orbSum g F k = Σ_{i<k} g^i F g^{k-i}` and `E = orbitSpec lam g k = k⁻¹ • Σ_{j<k} (λ⁻¹)^j • g^j`, one has `F O E F = k⁻¹ · F` and `O E F O E = k⁻¹ · (O E)`.  Hypotheses: `M` a `ℂ`-algebra, `k > 0`, `F*F = F`, `g^k = 1`, `λ^k = 1`, and the `k` conjugates of `F` pairwise orthogonal. -/
theorem OrbitCrux {M : Type} [Ring M] [Algebra ℂ M] (k : ℕ) (hk : 0 < k) (F g : M)
    (hF : F * F = F) (hg : g ^ k = 1)
    (horth : ∀ i j : ℕ, i < k → j < k → i ≠ j →
      (g ^ i * F * g ^ (k - i)) * (g ^ j * F * g ^ (k - j)) = 0)
    (lam : ℂ) (hlam : lam ^ k = 1) :
    (F * orbSum g F k * orbitSpec lam g k * F = algebraMap ℂ M ((k : ℂ)⁻¹) * F) ∧
    (orbSum g F k * orbitSpec lam g k * F * orbSum g F k * orbitSpec lam g k =
      algebraMap ℂ M ((k : ℂ)⁻¹) * (orbSum g F k * orbitSpec lam g k)) := by
  have hOO : orbSum g F k * orbSum g F k = orbSum g F k :=
    orbSum_mul_self k hk F g hF hg horth
  have hFO : F * orbSum g F k = F := orbSum_absorb k hk F g hF hg horth
  have hFEF := orbitCrux_FEF k hk F g hF hg horth lam hlam
  have hEFE := orbitCrux_EFE k hk F g hF hg horth lam hlam
  constructor
  · rw [hFO, hFEF, Algebra.smul_def]
  · calc orbSum g F k * orbitSpec lam g k * F * orbSum g F k * orbitSpec lam g k
        = orbSum g F k * orbitSpec lam g k * (F * orbSum g F k) * orbitSpec lam g k := by
          noncomm_ring
      _ = orbSum g F k * orbitSpec lam g k * F * orbitSpec lam g k := by rw [hFO]
      _ = orbSum g F k * (orbitSpec lam g k * F * orbitSpec lam g k) := by noncomm_ring
      _ = orbSum g F k * (((k : ℂ)⁻¹) • (orbSum g F k * orbitSpec lam g k)) := by rw [hEFE]
      _ = ((k : ℂ)⁻¹) • (orbSum g F k * (orbSum g F k * orbitSpec lam g k)) := by
          rw [mul_smul_comm]
      _ = ((k : ℂ)⁻¹) • (orbSum g F k * orbitSpec lam g k) := by
          rw [← mul_assoc, hOO]
      _ = algebraMap ℂ M ((k : ℂ)⁻¹) * (orbSum g F k * orbitSpec lam g k) := by
          rw [Algebra.smul_def]

end Work.KT.Psi

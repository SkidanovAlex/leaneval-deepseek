import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.Defs
import Submission.Work.Deep.Nibble.exists_edgePartition
import Submission.Work.Deep.Nibble.Blocks

/-!
# `Work.Deep.Nibble.exists_assemblyData`

The §7 assembly data for `lem:nibble2`: from the corrected margins
`NibbleMarginsStrong` we select the constants `κ, γp, δ, βp` and the number of
parts `K` of `AssemblyParams`, and obtain the `K`-fold partition `P` of the
edges of `𝓗'` of degree accuracy `δ` from `Work.Deep.Nibble.exists_edgePartition`.

The choices are `κ = γ²/3200`, `γp = γ/4`, `βp = κ/10 = γ²/32000`,
`δ = βp/8 = γ²/256000` and `K = ⌈1/κ⌉ = ⌈3200/γ²⌉` (this is the paper's
parameterisation `κ = γ²/(16C)`, `γp = γ/4` with `C = 200`).  The domination
field `hnbig` of `NibbleMarginsStrong` forces `γ ≤ 10⁻⁶` and
`γ^16 * n ≥ 10^400`, which is what makes the ~31 numeric fields of
`AssemblyParams` and the Chernoff bound of the partition step hold
simultaneously.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1000

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

/-- **The `AssemblyParams` bundle at the selected constants.**  Every numeric
field of `AssemblyParams` is a consequence of the margins
`NibbleMarginsStrong`; the choices of `κ, γp, δ, βp, K` are recorded in the
docstring of `exists_assemblyData`. -/
theorem assemblyParams_selected {n : ℕ} {D : ℝ} {r : ℕ} {β γ ε ρ ξ : ℝ}
    (hm : ErdosFaberLovaszConjecture.NibbleMarginsStrong n D r β γ ε ρ ξ) (hD : 0 < D) :
    ErdosFaberLovaszConjecture.AssemblyParams n D β γ ε ρ ξ
      (γ^2/3200) (γ/4) (γ^2/256000) (γ^2/32000) (Nat.ceil (3200/γ^2)) := by
  let K : ℕ := Nat.ceil (3200 / γ^2)
  change ErdosFaberLovaszConjecture.AssemblyParams n D β γ ε ρ ξ
      (γ^2/3200) (γ/4) (γ^2/256000) (γ^2/32000) K
  have hγ0 : 0 < γ := hm.base.hγ0
  have hγne : γ ≠ 0 := ne_of_gt hγ0
  have hρ0 : 0 < ρ := hm.base.hρ0
  have hε0 : 0 < ε := hm.base.hε0
  have hβ0 : 0 < β := hm.base.hβ0
  have hρ1 : ρ ≤ 1 := hm.base.hρ1
  have hγρ1 : 10 ^ 6 * γ ≤ ρ := hm.hγρ
  have hγ1 : γ ≤ 1 := by linarith
  have hε1 : ε ≤ 1 := by linarith [hm.hε]
  have hn8 : 8 ≤ n := hm.base.hn
  have hN8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
  have hN0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hN0' : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hN0
  have hγnonneg : (0:ℝ) ≤ γ := le_of_lt hγ0
  have hγ2pos : (0:ℝ) < γ^2 := by positivity
  have hD2 : (n:ℝ)/2 ≤ D := hm.hDlin
  have hDhigh : D ≤ (n:ℝ) := hm.base.hDhigh
  have hNmD : ρ * (n:ℝ) ≤ (n:ℝ) - D := by have := hm.hDgap; nlinarith [this]
  have hβhalf : β ≤ 1/2 := by
    have h1 := pow_le_one₀ hγnonneg hγ1 (n := 4)
    have h := hm.hβ4
    linarith
  -- the chain from `hnbig`
  have hterm16 : 10^400 * (γ⁻¹)^16 ≤ (n:ℝ) := by
    have hle : (γ⁻¹)^16 ≤ (ρ⁻¹)^6 + (γ⁻¹)^16 + (γ*ρ*ε)⁻¹ + ((γ*ρ*ε)⁻¹)^2 + (r:ℝ) := by
      have h1 : 0 ≤ (ρ⁻¹)^6 := by positivity
      have h2 : 0 ≤ (γ*ρ*ε)⁻¹ := by positivity
      have h3 : 0 ≤ ((γ*ρ*ε)⁻¹)^2 := by positivity
      have h4 : 0 ≤ ((r:ℝ)) := by positivity
      linarith
    calc 10^400 * (γ⁻¹)^16
        ≤ 10^400 * ((ρ⁻¹)^6 + (γ⁻¹)^16 + (γ*ρ*ε)⁻¹ + ((γ*ρ*ε)⁻¹)^2 + (r:ℝ)) := by
          gcongr
      _ ≤ (n:ℝ) := hm.hnbig
  have hγ16N : (10:ℝ)^400 ≤ γ^16 * (n:ℝ) := by
    have heq : γ^16 * (10^400 * (γ⁻¹)^16) = 10^400 := by
      have hthis : γ^16 * (γ⁻¹)^16 = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hγne, one_pow]
      rw [mul_comm (10^400) ((γ⁻¹)^16), ← mul_assoc, hthis, one_mul]
    have hmul := mul_le_mul_of_nonneg_left hterm16 (show (0:ℝ) ≤ γ^16 by positivity)
    linarith [heq, hmul]
  have hγ4N : (10:ℝ)^400 ≤ γ^4 * (n:ℝ) := by
    have hle : γ^16 ≤ γ^4 := pow_le_pow_of_le_one hγnonneg hγ1 (by norm_num)
    have h := mul_le_mul_of_nonneg_right hle hN0'
    linarith [hγ16N, h]
  have hγ2N : (10:ℝ)^400 ≤ γ^2 * (n:ℝ) := by
    have hle : γ^16 ≤ γ^2 := pow_le_pow_of_le_one hγnonneg hγ1 (by norm_num)
    have h := mul_le_mul_of_nonneg_right hle hN0'
    linarith [hγ16N, h]
  have hγ3N : (10:ℝ)^400 ≤ γ^3 * (n:ℝ) := by
    have hle : γ^16 ≤ γ^3 := pow_le_pow_of_le_one hγnonneg hγ1 (by norm_num)
    have h := mul_le_mul_of_nonneg_right hle hN0'
    linarith [hγ16N, h]
  have hγρN : (10:ℝ)^400 ≤ γ*ρ*(n:ℝ) := by
    have htermγρε : 10^400 * (γ*ρ*ε)⁻¹ ≤ (n:ℝ) := by
      have hle : (γ*ρ*ε)⁻¹ ≤ (ρ⁻¹)^6 + (γ⁻¹)^16 + (γ*ρ*ε)⁻¹ + ((γ*ρ*ε)⁻¹)^2 + (r:ℝ) := by
        have h1 : 0 ≤ (ρ⁻¹)^6 := by positivity
        have h2 : 0 ≤ (γ⁻¹)^16 := by positivity
        have h3 : 0 ≤ ((γ*ρ*ε)⁻¹)^2 := by positivity
        have h4 : 0 ≤ ((r:ℝ)) := by positivity
        linarith
      calc 10^400 * (γ*ρ*ε)⁻¹
          ≤ 10^400 * ((ρ⁻¹)^6 + (γ⁻¹)^16 + (γ*ρ*ε)⁻¹ + ((γ*ρ*ε)⁻¹)^2 + (r:ℝ)) := by
            gcongr
        _ ≤ (n:ℝ) := hm.hnbig
    have hγρεN : (10:ℝ)^400 ≤ γ*ρ*ε*(n:ℝ) := by
      have heq : γ*ρ*ε * (10^400 * (γ*ρ*ε)⁻¹) = 10^400 := by
        rw [mul_comm (10^400), ← mul_assoc,
          mul_inv_cancel₀ (by positivity : γ*ρ*ε ≠ 0), one_mul]
      have hmul := mul_le_mul_of_nonneg_left htermγρε (show (0:ℝ) ≤ γ*ρ*ε by positivity)
      linarith [heq, hmul]
    have hle : γ*ρ*ε ≤ γ*ρ := by
      have := mul_le_mul_of_nonneg_left hε1 (show (0:ℝ) ≤ γ*ρ by positivity)
      linarith [this]
    have h := mul_le_mul_of_nonneg_right hle hN0'
    linarith [hγρεN, h]
  have hγ2ρN : 3200 ≤ γ^2*ρ*(n:ℝ) := by
    nlinarith [hγρ1, hγ3N, hγ0, hρ0, hN0']
  -- `s = √n`
  set s : ℝ := Real.sqrt (n:ℝ) with hs_def
  have hs2 : s^2 = (n:ℝ) := by rw [hs_def, Real.sq_sqrt hN0']
  have hs0 : (0:ℝ) ≤ s := by rw [hs_def]; exact Real.sqrt_nonneg _
  have hs1 : (1:ℝ) ≤ s := by
    rw [hs_def, Real.one_le_sqrt]
    linarith [hN8]
  have hs2le : (2:ℝ) ≤ s := by
    rw [hs_def]
    exact (Real.le_sqrt (by norm_num : (0:ℝ) ≤ 2) hN0').mpr (by nlinarith [hN8])
  have hγ12N : (10:ℝ)^400 ≤ γ^12 * (n:ℝ) := by
    have hle : γ^16 ≤ γ^12 := pow_le_pow_of_le_one hγnonneg hγ1 (by norm_num)
    have h := mul_le_mul_of_nonneg_right hle hN0'
    linarith [hγ16N, h]
  have hγ6s : (10:ℝ)^200 ≤ γ^6 * s := by
    have hsq : ((10:ℝ)^200)^2 ≤ (γ^6 * s)^2 := by
      have he : (γ^6 * s)^2 = γ^12 * (n:ℝ) := by
        rw [mul_pow, hs2, ← pow_mul]
      have he2 : ((10:ℝ)^200)^2 = (10:ℝ)^400 := by norm_num
      rw [he, he2]
      exact hγ12N
    have h1 : ((10:ℝ)^200) ≤ |γ^6 * s| := by
      have := sq_le_sq.mp hsq
      simpa using this
    rwa [abs_of_nonneg (by positivity)] at h1
  have hγ2s : (10:ℝ)^200 ≤ γ^2 * s := by
    have hle : γ^6 ≤ γ^2 := pow_le_pow_of_le_one hγnonneg hγ1 (by norm_num)
    have h := mul_le_mul_of_nonneg_right hle hs0
    linarith [hγ6s, h]
  -- `K` facts
  have hK1 : 3200 / γ^2 ≤ (K:ℝ) := Nat.le_ceil _
  have hK2 : (K:ℝ) < 3200/γ^2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hKpos : (0:ℝ) < (K:ℝ) := by
    have : 0 < K := by
      rw [show K = Nat.ceil (3200/γ^2) from rfl]
      exact Nat.ceil_pos.mpr (by positivity)
    exact_mod_cast this
  have hKle : (K:ℝ) ≤ 6400/γ^2 := by
    rw [le_div_iff₀ hγ2pos]
    have h1 : (K:ℝ)*γ^2 < (3200/γ^2 + 1)*γ^2 := mul_lt_mul_of_pos_right hK2 hγ2pos
    have h2 : (3200/γ^2 + 1)*γ^2 = 3200 + γ^2 := by field_simp
    have h3 : γ^2 ≤ 3200 := by nlinarith [hγ1, hγnonneg]
    nlinarith [h1, h2, h3]
  have hKle' : (K:ℝ) * γ^2 ≤ 6400 := (le_div_iff₀ hγ2pos).mp hKle
  have hKceil : 1 ≤ (K:ℝ)*(γ^2/3200) := by
    have h := mul_le_mul_of_nonneg_right hK1 (show (0:ℝ) ≤ γ^2/3200 by positivity)
    have he : (3200/γ^2) * (γ^2/3200) = 1 := by field_simp
    linarith [h, he]
  have hKge2 : 2 ≤ K := by
    rw [show K = Nat.ceil (3200/γ^2) from rfl, ← Nat.cast_le (α := ℝ)]
    have h24 : (2:ℝ) ≤ (3200/γ^2) := by rw [le_div_iff₀ hγ2pos]; nlinarith [hγ1]
    linarith [hK1]
  have hKleN : (K:ℝ) ≤ (n:ℝ) := by
    have h : 6400/γ^2 ≤ (n:ℝ) := by rw [div_le_iff₀ hγ2pos]; nlinarith [hγ2N]
    linarith [hKle, h]
  have hKleD2 : 2*(K:ℝ) ≤ D := by
    have h1 : 2*(K:ℝ) ≤ 12800/γ^2 := by rw [le_div_iff₀ hγ2pos]; nlinarith [hKle']
    have h2 : 12800/γ^2 ≤ D := by
      rw [div_le_iff₀ hγ2pos]
      have h3 := mul_le_mul_of_nonneg_left hD2 (show (0:ℝ) ≤ γ^2 by positivity)
      have h4 : γ^2*((n:ℝ)/2) = (γ^2*(n:ℝ))/2 := by ring
      nlinarith [hγ2N, h3, h4]
    linarith [h1, h2]
  have hβK2 : β*(K:ℝ) ≤ γ^2/64000 := by
    have h1 : β*(K:ℝ) ≤ (γ^4/10^12)*(K:ℝ) :=
      mul_le_mul_of_nonneg_right hm.hβ4 (le_of_lt hKpos)
    nlinarith [h1, hKle', hγ0, hγnonneg]
  have hβK : β*(K:ℝ) ≤ γ^2/32000 := le_trans hβK2 (by nlinarith [sq_nonneg γ])
  -- the `AssemblyParams` fields
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · nlinarith [hγ1]
  · nlinarith [hγρ1]
  · nlinarith [hm.hγρε, hγ0, hρ0, hε0]
  · nlinarith [sq_nonneg γ]
  · positivity
  · linarith
  · nlinarith [hγ1, hγ0]
  · nlinarith [hγρ1]
  · nlinarith [hm.hγρε]
  · nlinarith [hm.hξ, hε1, hγ0, hρ0, hε0]
  · nlinarith [hγρN]
  · nlinarith [hγ2N]
  · positivity
  · nlinarith [hγ1]
  · positivity
  · nlinarith [hγ1]
  · -- hβp
    have hγ4D : (5:ℝ)*10^399 ≤ γ^4 * D := by
      have h1 := mul_le_mul_of_nonneg_left hD2 (show (0:ℝ) ≤ γ^4 by positivity)
      have h2 : γ^4 * ((n:ℝ)/2) = (γ^4*(n:ℝ))/2 := by ring
      nlinarith [hγ4N, h1, h2]
    have hβpraw : (4*(K:ℝ))/D ≤ γ^2/128000 := by
      rw [div_le_div_iff₀ hD (by norm_num : (0:ℝ) < 128000)]
      have hkey : γ^2 * (4*(K:ℝ)*128000) ≤ γ^2 * (γ^2*D) := by
        have h1 : γ^2 * (4*(K:ℝ)*128000) ≤ 25600*128000 := by nlinarith [hKle']
        have h2 : (25600*128000:ℝ) ≤ γ^2*(γ^2*D) := by
          have h3 : γ^2*(γ^2*D) = γ^4*D := by ring
          rw [h3]; nlinarith [hγ4D]
        linarith [h1, h2]
      exact (mul_le_mul_iff_right₀ hγ2pos).mp hkey
    have hβpaux : 4*((K:ℝ)/D) ≤ γ^2/128000 := by
      have he : 4*((K:ℝ)/D) = (4*(K:ℝ))/D := by ring
      rw [he]; exact hβpraw
    have hβpt : 4*β ≤ γ^2/128000 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 128000)]
      have h := hm.hβ4
      have h4 := pow_le_one₀ hγnonneg hγ1 (n := 4)
      nlinarith [h, h4]
    have hsum : 4*(γ^2/256000) + 4*β + 4*((K:ℝ)/D) ≤ γ^2/32000 := by
      have hA : 4*(γ^2/256000) = γ^2/64000 := by ring
      linarith [hβpaux, hβpt, hA]
    calc 4*(γ^2/256000 + β + (K:ℝ)/D) = 4*(γ^2/256000) + 4*β + 4*((K:ℝ)/D) := by ring
      _ ≤ γ^2/32000 := hsum
  · linarith
  · exact hKge2
  · -- hKlow
    have hKinv : γ^2/6400 ≤ 1/(K:ℝ) := by
      have := one_div_le_one_div_of_le hKpos hKle
      rwa [one_div_div] at this
    have hKlow' : s ≤ D/(K:ℝ) := by
      have hstep : (γ^2/6400)*D ≤ D/(K:ℝ) := by
        have h := mul_le_mul_of_nonneg_right hKinv (le_of_lt hD)
        have he : (1/(K:ℝ))*D = D/(K:ℝ) := by ring
        linarith [h, he]
      have hstep2 : s ≤ (γ^2/6400)*D := by
        have h1 := mul_le_mul_of_nonneg_left hD2 (show (0:ℝ) ≤ γ^2/6400 by positivity)
        have h2 : (γ^2/6400)*((n:ℝ)/2) = γ^2*s^2/12800 := by rw [← hs2]; ring
        have h6 : (10:ℝ)^200 * s ≤ γ^2*s^2 := by nlinarith [hγ2s, hs0]
        have h5 : s ≤ (10:ℝ)^200*s/12800 := by nlinarith [hs1, hs0]
        linarith [h1, h2, h6, h5]
      linarith [hstep, hstep2]
    simpa [hs_def, Real.sqrt_eq_rpow] using hKlow'
  · exact hKceil
  · -- hKfloor
    have hKfloor' : s + 1 ≤ (γ^2/3200)*D := by
      have h1 := mul_le_mul_of_nonneg_left hD2 (show (0:ℝ) ≤ γ^2/3200 by positivity)
      have h2 : (γ^2/3200)*((n:ℝ)/2) = γ^2*s^2/6400 := by rw [← hs2]; ring
      have h6 : (10:ℝ)^200 * s ≤ γ^2*s^2 := by nlinarith [hγ2s, hs0]
      have h5 : s + 1 ≤ (10:ℝ)^200*s/6400 := by nlinarith [hs2le, hs0]
      linarith [h1, h2, h6, h5]
    simpa [hs_def, Real.sqrt_eq_rpow] using hKfloor'
  · -- hKround
    have h1 := mul_le_mul_of_nonneg_left hNmD (show (0:ℝ) ≤ γ^2/3200 by positivity)
    have h2 : (γ^2/3200)*(ρ*(n:ℝ)) = γ^2*ρ*(n:ℝ)/3200 := by ring
    linarith [h1, h2, hγ2ρN]
  · -- hβD'
    have h1 : β*D ≤ (γ^4/10^12)*(n:ℝ) := by
      have h2 : β*D ≤ β*(n:ℝ) := mul_le_mul_of_nonneg_left hDhigh (le_of_lt hβ0)
      have h3 : β*(n:ℝ) ≤ (γ^4/10^12)*(n:ℝ) := mul_le_mul_of_nonneg_right hm.hβ4 hN0'
      linarith [h2, h3]
    nlinarith [h1]
  · exact hβK
  · -- hβpfloor
    have hKl : 2 ≤ D/(K:ℝ) := by rw [le_div_iff₀ hKpos]; linarith [hKleD2]
    have hb1 : β*D ≤ (γ^2/64000) * (D/(K:ℝ)) := by
      have h := mul_le_mul_of_nonneg_right hβK2 (show (0:ℝ) ≤ D/(K:ℝ) by positivity)
      have he : β*(K:ℝ)*(D/(K:ℝ)) = β*D := by field_simp
      linarith [h, he]
    have hb2 : (γ^2/64000)*(D/(K:ℝ)) ≤ (γ^2/32000)*(D/(K:ℝ) - 1) := by
      have h2 : D/(K:ℝ) ≤ 2*(D/(K:ℝ)-1) := by linarith [hKl]
      have he2 : (γ^2/32000)*(D/(K:ℝ)-1) = 2*((γ^2/64000)*(D/(K:ℝ)-1)) := by ring
      have h3 := mul_le_mul_of_nonneg_left h2 (show (0:ℝ) ≤ γ^2/64000 by positivity)
      linarith [h3, he2]
    linarith [hb1, hb2]
  · nlinarith [sq_nonneg γ]
  · -- hKup
    have h1 : (n:ℝ) ≤ (γ^2/3200)*(n:ℝ)*(K:ℝ) := by nlinarith [hKceil, hN0']
    linarith [hDhigh, h1]
  · -- hCher
    have hX : 1000 * s ≤ (3*(γ^2/256000)^2*(1-β)*D)/(8*(K:ℝ)) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 8*(K:ℝ))]
      have h8K : 8*(K:ℝ)*γ^2 ≤ 51200 := by nlinarith [hKle']
      have h6 : (10:ℝ)^200 * s ≤ γ^6 * s^2 := by nlinarith [hγ6s, hs0]
      have hβ1 : (1:ℝ)/2 ≤ 1 - β := by linarith [hβhalf]
      have hDs : s^2/2 ≤ D := by rw [hs2]; exact hD2
      have hscale : γ^2 * (1000*s*(8*(K:ℝ))) ≤ γ^2 * (3*(γ^2/256000)^2*(1-β)*D) := by
        have heL : γ^2 * (1000*s*(8*(K:ℝ))) = 1000*s*((8*(K:ℝ))*γ^2) := by ring
        have hL : 1000*s*((8*(K:ℝ))*γ^2) ≤ 1000*s*51200 :=
          mul_le_mul_of_nonneg_left h8K (by positivity)
        have hR : 1000*s*51200 ≤ γ^2 * (3*(γ^2/256000)^2*(1-β)*D) := by
          have he : γ^2 * (3*(γ^2/256000)^2*(1-β)*D) = 3*γ^6*(1-β)*D/256000^2 := by ring
          rw [he, le_div_iff₀ (by norm_num : (0:ℝ) < 256000^2)]
          have hkey : (1/2)*(s^2/2) ≤ (1-β)*D := by
            calc (1/2)*(s^2/2) ≤ (1-β)*(s^2/2) :=
                  mul_le_mul_of_nonneg_right hβ1 (by positivity)
              _ ≤ (1-β)*D := mul_le_mul_of_nonneg_left hDs (by linarith [hβ1])
          have h1 : 3*γ^6*(1/2)*(s^2/2) ≤ 3*γ^6*(1-β)*D := by
            have h := mul_le_mul_of_nonneg_left hkey (show (0:ℝ) ≤ 3*γ^6 by positivity)
            linarith [h]
          have h2 : 1000*s*51200*256000^2 ≤ 3*γ^6*(1/2)*(s^2/2) := by
            nlinarith [h6, hs0]
          linarith [h1, h2]
        rw [heL]; linarith [hL, hR]
      exact (mul_le_mul_iff_right₀ hγ2pos).mp hscale
    have hx4pos : (0:ℝ) < (1000*s)^4 := by positivity
    have hexp2 : Real.exp (-(1000*s)) * (1000*s)^4 ≤ 24 := by
      have h2 : (1000*s)^4 / 24 ≤ Real.exp (1000*s) := by
        have h := Real.pow_div_factorial_le_exp (1000*s) (by positivity) 4
        have h4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num
        simpa only [h4] using h
      have h1 : Real.exp (-(1000*s)) * Real.exp (1000*s) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have hmm := mul_le_mul_of_nonneg_left h2 (le_of_lt (Real.exp_pos (-(1000*s))))
      have hkey : Real.exp (-(1000*s)) * (1000*s)^4 / 24 ≤ 1 := by
        have he : Real.exp (-(1000*s)) * (1000*s)^4 / 24
            = Real.exp (-(1000*s)) * ((1000*s)^4 / 24) := by ring
        rw [he]; linarith [hmm, h1]
      have hfin := mul_le_mul_of_nonneg_right hkey (le_of_lt (by norm_num : (0:ℝ) < 24))
      have he2 : Real.exp (-(1000*s)) * (1000*s)^4 / 24 * 24
          = Real.exp (-(1000*s)) * (1000*s)^4 := by ring
      linarith [hfin, he2]
    calc 2 * ((n:ℝ) * (K:ℝ)) * Real.exp (-(3*(γ^2/256000)^2*(1-β)*D)/(8*(K:ℝ)))
        ≤ 2 * ((n:ℝ) * (n:ℝ)) * Real.exp (-(1000*s)) := by
          have hexp1 : Real.exp (-(3*(γ^2/256000)^2*(1-β)*D)/(8*(K:ℝ)))
              ≤ Real.exp (-(1000*s)) := by
            apply Real.exp_le_exp.mpr
            have he : -(3*(γ^2/256000)^2*(1-β)*D)/(8*(K:ℝ))
                = -((3*(γ^2/256000)^2*(1-β)*D)/(8*(K:ℝ))) := by ring
            rw [he]; exact neg_le_neg hX
          have h1 : 2*((n:ℝ)*(K:ℝ)) ≤ 2*((n:ℝ)*(n:ℝ)) := by nlinarith [hKleN, hN0']
          have h3 : (0:ℝ) ≤ Real.exp (-(1000*s)) := le_of_lt (Real.exp_pos _)
          have h4 : (0:ℝ) ≤ 2*((n:ℝ)*(K:ℝ)) := by positivity
          nlinarith [h1, h3, h4, hexp1]
      _ ≤ 2 * ((n:ℝ) * (n:ℝ)) * (24/(1000*s)^4) := by
          have h2 : Real.exp (-(1000*s)) ≤ 24/(1000*s)^4 := by
            rw [le_div_iff₀ hx4pos]; exact hexp2
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ < 1 := by
          have hs4 : s^4 = ((n:ℝ))^2 := by rw [show s^4 = (s^2)^2 by ring, hs2]
          have hx4 : (1000*s)^4 = 10^12 * ((n:ℝ))^2 := by
            rw [show (1000*s)^4 = (1000:ℝ)^4 * s^4 by ring, hs4]
            norm_num
          rw [hx4]
          have heq : 2 * ((n:ℝ) * (n:ℝ)) * (24 / (10^12 * ((n:ℝ))^2)) = 48/10^12 := by
            field_simp
            ring
          rw [heq]
          norm_num
  · -- hfam
    have hN1 : 1 < (n:ℝ) := by linarith [hN8]
    have hlogN : (2:ℝ) ≤ Real.log (n:ℝ) := by
      have h1 : Real.log (8:ℝ) ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) hN8
      have h2 : Real.log (8:ℝ) = Real.log 2 * 3 := by
        rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
        ring
      have h3 : (2:ℝ) < Real.log 2 * 3 := by linarith [Real.log_two_gt_d9]
      linarith [h1, h2, h3]
    have hstep : (n:ℝ)^(2:ℝ) ≤ (n:ℝ)^Real.log (n:ℝ) :=
      (Real.rpow_le_rpow_left_iff hN1).mpr hlogN
    have hsq : (n:ℝ)^2 ≤ (n:ℝ)^(2:ℝ) := le_of_eq (Real.rpow_two (n:ℝ)).symm
    have hfin : 2*(n:ℝ) + 4 ≤ (n:ℝ)^2 := by nlinarith [hN8]
    exact le_trans hfin (le_trans hsq hstep)

/-- **The assembly data selected from the corrected margins.**

Given the cone's corrected margins
`ErdosFaberLovaszConjecture.NibbleMarginsStrong n D r β γ ε ρ ξ`
(`Submission/EFL/Nibble.lean`: the `γρε`-relative hierarchy, the window relation
`hγρε : 10 γ ≤ ρ ε`, `hDgap : D ≤ (1-ρ)n`, and the strengthened domination
condition `hnbig`, whose terms `(γ⁻¹)^16`, `(ρ⁻¹)^6`, `(γρε)⁻¹` keep `γ` and `ρ`
from being too small relative to `n`), a sub-multi-hypergraph `𝓗'` whose
degrees are `(1±β)D`, and `D > 0`, there are

* a constant `κ`, a pseudorandomness parameter `γp`, a partition accuracy `δ`, a
  tolerance `βp` and a number of parts `K` satisfying `AssemblyParams` (see the
  docstring of `AssemblyParams`: the `InternalMargins`/`CrossingMargins` fields
  at `γ_abs = γp`, the bracketing `γ ≤ 4γp`, `γp + 2κ ≤ γ`, the rounding slack
  `hKceil`, `hKfloor`, `hKround`, the seed-size conditions `hβD'`, `hβK`,
  `hβpfloor`, the slack `hκγ2'` for the loose singleton edges, the Chernoff
  bound `hCher`, and `hfam`), and
* a `K`-fold partition `P` of the edges of `𝓗'` into parts of degree accuracy
  `δ` (`Work.Deep.Nibble.exists_edgePartition`, applicable once `hCher` and
  `hdeg` are in hand).

Suitable choices: `γp := γ/4`, `κ := γ²/(16C)` with `C := 200` (the statement
below uses `κ = γ²/3200`, `βp = κ/10`, `δ = βp/8`, `K := ⌈1/κ⌉ = ⌈3200/γ²⌉`).
The domination condition `hnbig` is what makes the Chernoff bound `hCher`, the
`n_i ≥ √n` condition `hKfloor` and the seed-size floor `hβpfloor` hold
simultaneously.  (A previous proof of this statement used two fields `hγρε'`,
`hnup` that have since been replaced in the cone by the strengthened `hnbig`;
the projection of those two fields is gone.) -/
theorem exists_assemblyData {n : ℕ} (𝓗' : ErdosFaberLovaszConjecture.MultiHypergraph n)
    {D : ℝ} {r : ℕ} {β γ ε ρ ξ : ℝ}
    (hm : ErdosFaberLovaszConjecture.NibbleMarginsStrong n D r β γ ε ρ ξ)
    (hD : 0 < D)
    (hdeg : ∀ w : Fin n, |((𝓗'.deg w : ℝ)) - D| ≤ β * D) :
    ∃ (κ γp δ βp : ℝ) (K : ℕ) (P : ErdosFaberLovaszConjecture.EdgePartition 𝓗' K),
      ErdosFaberLovaszConjecture.AssemblyParams n D β γ ε ρ ξ κ γp δ βp K ∧
      (∀ i w, |(((P.part i).deg w : ℝ)) - (𝓗'.deg w : ℝ) / (K : ℝ)| ≤
        δ * ((𝓗'.deg w : ℝ) / (K : ℝ))) := by
  have hparams := assemblyParams_selected hm hD
  have hβhalf : β ≤ 1/2 := by
    have hγ0 : 0 < γ := hm.base.hγ0
    have hγ1 : γ ≤ 1 := by
      have h1 := hm.hγρ
      have h2 := hm.base.hρ1
      linarith
    have h1 := pow_le_one₀ (le_of_lt hγ0) hγ1 (n := 4)
    have h := hm.hβ4
    linarith
  have hCher : 2 * ((n:ℝ) * ((Nat.ceil (3200/γ^2)) : ℝ)) *
      Real.exp (-(3 * (γ^2/256000)^2 * ((1-β)*D)) / (8 * ((Nat.ceil (3200/γ^2)) : ℝ))) < 1 := by
    have h := hparams.hCher
    simpa only [mul_assoc] using h
  obtain ⟨P, hPacc⟩ := exists_edgePartition 𝓗' hparams.hK hparams.hδ0 hparams.hδ1
    hβhalf hdeg hCher
  exact ⟨γ^2/3200, γ/4, γ^2/256000, γ^2/32000, Nat.ceil (3200/γ^2), P, hparams, hPacc⟩

end

end Work.Deep.Nibble

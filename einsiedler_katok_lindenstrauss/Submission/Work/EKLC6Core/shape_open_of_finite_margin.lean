import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.shape_pastSig_eq
import Submission.Work.EKLC6Core.contract_rate
import Submission.Work.EKLComp.LeafDefs

/-!
# `Work.EKLC6Core.shape_open_of_finite_margin`

**Openness of the shape of the descending plaque algebra from a finite margin.**

Let `U ≤ SL₃(ℝ)` be horospherical, `a = aDiag t`, `T = (aDiag t ·)` and let `M` be a
σ-algebra on `X₃` whose atoms along the orbit of `x` are plaques — relatively open in `U` and
bounded by the ball `Uball U ρ` at the (single) time `k`.  Assume finally that from some time `N`
on, the shape at the orbit point `Tⁿ x` contains the ball `Uball U (c μⁿ)`, where `λ ∈ [0,1)` is
the contraction rate of `a` on `U` and `λ < μ < 1`.

Then the atom of `x` for the *descending* σ-algebra `A = ⨆ₙ (Tⁿ)⁻¹ M` has relatively open shape.

The mechanism is the *finite margin*: the shape of `A` at `x` is the set of `u ∈ U` whose whole
conjugated orbit `θₙ(u) = aⁿ u a⁻ⁿ` stays in the transported shapes `Sₙ = shape M U (Tⁿ x)`
(`Work.EKLC6Core.shape_pastSig_eq`).  Because `θₖ(u) ∈ Sₖ ⊆ Uball U ρ` is one of the constraints,
the contraction `hrate` squeezes `θₙ(u) ∈ Uball U (ρ λ^{n-k})` for all `n ≥ k`, and since
`λ^{n-k} ≪ μⁿ` the margin hypothesis makes *all* constraints beyond a finite threshold `K`
automatic.  Hence the shape is the intersection of the finitely many relatively open constraints
`{u ∈ U | θₙ(u) ∈ Wₙ}` (`n < K`), which is the trace on `U` of an open subset of `SL₃(ℝ)`.

This differs from `Work.EKLC6Core.isOpen_shape_pastSig_of_margin` (`margin_shape.lean`) in that
the boundedness hypothesis is imposed at an arbitrary time `k` (and the margin holds eventually),
which is what the entropy computation of component C6 supplies.
-/

open MeasureTheory Topology Filter

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **Elementary asymptotic comparison.**  With `0 ≤ λ < μ`, `c > 0` and any `ρ`, `k ∈ ℕ`, for
all sufficiently large `n` the contracted radius `ρ λ^{n-k}` is dominated by `c μⁿ`.  (For `λ = 0`
this is immediate since the left side vanishes once `n > k`; in general `λ^{n-k}/μⁿ =
(1/λ^k)(λ/μ)ⁿ → 0`.) -/
private theorem geometric_margin_bound {lam mu c : ℝ} (ρ : ℝ) (hlam0 : 0 ≤ lam)
    (hlammu : lam < mu) (hc : 0 < c) (k N : ℕ) :
    ∃ K : ℕ, k < K ∧ N ≤ K ∧ ∀ n : ℕ, K ≤ n → ρ * lam ^ (n - k) ≤ c * mu ^ n := by
  have hmu0 : 0 < mu := lt_of_le_of_lt hlam0 hlammu
  set q : ℝ := lam / mu with hqdef
  have hq0 : 0 ≤ q := div_nonneg hlam0 (le_of_lt hmu0)
  have hq1 : q < 1 := (div_lt_one hmu0).mpr hlammu
  have hlim : Tendsto (fun n : ℕ => q ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hlim2 : Tendsto (fun n : ℕ => ρ * q ^ n) atTop (nhds (ρ * 0)) := hlim.const_mul ρ
  have hcmk : 0 < c * mu ^ k := mul_pos hc (pow_pos hmu0 k)
  have hev : ∀ᶠ n : ℕ in atTop, ρ * q ^ n < c * mu ^ k :=
    hlim2.eventually (isOpen_Iio.mem_nhds (by simpa using hcmk))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hev
  refine ⟨max (max N (N₁ + k)) (k + 1), by omega, by omega, ?_⟩
  intro n hn
  have hkn : k ≤ n := by omega
  have hN₁' : N₁ ≤ n - k := by omega
  have hb : ρ * q ^ (n - k) ≤ c * mu ^ k := le_of_lt (hN₁ (n - k) hN₁')
  have hpoweq : lam ^ (n - k) = q ^ (n - k) * mu ^ (n - k) := by
    rw [hqdef, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (ne_of_gt hmu0))]
  have hkn' : k + (n - k) = n := Nat.add_sub_cancel' hkn
  calc ρ * lam ^ (n - k) = ρ * (q ^ (n - k) * mu ^ (n - k)) := by rw [hpoweq]
    _ = (ρ * q ^ (n - k)) * mu ^ (n - k) := by ring
    _ ≤ (c * mu ^ k) * mu ^ (n - k) :=
          mul_le_mul_of_nonneg_right hb (pow_nonneg (le_of_lt hmu0) _)
    _ = c * mu ^ n := by rw [mul_assoc, ← pow_add, hkn']

theorem shape_open_of_finite_margin {U : Subgroup Work.EKLContract.SL3} {t : Fin 3 → ℝ}
    (hU : Work.EKLContract.IsHoro U) {M : MeasurableSpace Work.EKLContract.X3}
    {x : Work.EKLContract.X3} {k : ℕ} {c ρ lam mu : ℝ} (hc : 0 < c) (hρ : 0 < ρ)
    (hlam0 : 0 ≤ lam) (hlammu : lam < mu) (hmu1 : mu < 1)
    (hrate : ∀ n : ℕ, ∀ u : Work.EKLContract.SL3, u ∈ U →
      u ∈ Work.EKLComp.Uball U ρ →
      Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹
        ∈ Work.EKLComp.Uball U (ρ * lam ^ n))
    (hopen : ∀ n : ℕ, ∃ W : Set Work.EKLContract.SL3, IsOpen W ∧
      Work.EKLContract.shape M U (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x)
        = W ∩ (U : Set Work.EKLContract.SL3))
    (hbddk : Work.EKLContract.shape M U (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[k]) x)
      ⊆ Work.EKLComp.Uball U ρ)
    (hmargin : ∃ N : ℕ, ∀ n ≥ N, Work.EKLComp.Uball U (c * mu ^ n) ⊆
      Work.EKLContract.shape M U (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x)) :
    ∃ O : Set Work.EKLContract.SL3, IsOpen O ∧
      Work.EKLContract.shape (⨆ n : ℕ, MeasurableSpace.comap
        ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) M) U x
        = O ∩ (U : Set Work.EKLContract.SL3) := by
  classical
  -- the relatively open shapes along the orbit, `Sₙ = shape M U (Tⁿ x)`, are traces of the
  -- open sets `W n`
  choose W hWopen hWeq using hopen
  obtain ⟨N, hN⟩ := hmargin
  -- the finite threshold `K` beyond which the contracted radius is dominated by the margin
  obtain ⟨K, hkK, hNK, hKbound⟩ := geometric_margin_bound ρ hlam0 hlammu hc k N
  refine ⟨⋂ n ∈ Finset.range K, {g : SL3 | aDiag t ^ n * g * (aDiag t ^ n)⁻¹ ∈ W n},
    isOpen_biInter_finset (fun n _ => (hWopen n).preimage (by fun_prop)), ?_⟩
  -- the shape of the descending σ-algebra is the set of `u` whose conjugated orbit stays in `Sₙ`
  rw [shape_pastSig_eq hU x]
  ext u
  constructor
  · -- `⊆`: drop the constraints beyond the threshold
    rintro ⟨huU, hu⟩
    refine ⟨Set.mem_biInter (fun n _ => ((hWeq n) ▸ hu n).1), huU⟩
  · -- `⊇`: only the constraints with `n < K` matter; the rest are automatic
    rintro ⟨huO, huU⟩
    rw [Set.mem_iInter₂] at huO
    refine ⟨huU, fun n => ?_⟩
    rw [hWeq n]
    refine ⟨?_, conj_pow_mem_U hU huU n⟩
    by_cases hn : n < K
    · exact huO n (Finset.mem_range.mpr hn)
    · -- `n ≥ K`: the level-`k` constraint bounds `θₖ(u)`, and contraction squeezes all the rest
      push Not at hn
      have hkn : k ≤ n := by omega
      have hkW : aDiag t ^ k * u * (aDiag t ^ k)⁻¹ ∈ W k := huO k (Finset.mem_range.mpr hkK)
      have hkS : aDiag t ^ k * u * (aDiag t ^ k)⁻¹
          ∈ shape M U (((fun y : X3 => aDiag t • y)^[k]) x) := by
        rw [hWeq k]; exact ⟨hkW, conj_pow_mem_U hU huU k⟩
      have hkball := hbddk hkS
      have hstep := hrate (n - k) (aDiag t ^ k * u * (aDiag t ^ k)⁻¹)
        (conj_pow_mem_U hU huU k) hkball
      have hconj : aDiag t ^ (n - k) * (aDiag t ^ k * u * (aDiag t ^ k)⁻¹)
            * (aDiag t ^ (n - k))⁻¹ = aDiag t ^ n * u * (aDiag t ^ n)⁻¹ := by
        have e : aDiag t ^ n = aDiag t ^ (n - k) * aDiag t ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hkn]
        rw [e, mul_inv_rev]; group
      rw [hconj] at hstep
      have hmem : aDiag t ^ n * u * (aDiag t ^ n)⁻¹
          ∈ shape M U (((fun y : X3 => aDiag t • y)^[n]) x) :=
        hN n (by omega) (Work.EKLComp.Uball_mono (hKbound n hn) hstep)
      rw [hWeq n] at hmem
      exact hmem.1

end Work.EKLC6Core

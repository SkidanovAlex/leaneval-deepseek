import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.detL_GamMix
import Submission.Work.HP.Vero.finrank_latOrth
import Submission.Work.HP.lam_basic
import Submission.Work.HP.MDEstimates.rk_projScale

set_option autoImplicit false

noncomputable section

open Filter Finset MeasureTheory

namespace Work.HP.MM2

open Work.HP

/-- Auxiliary comparison of successive minima: if the lattice `M` contains `Q` times the lattice
`L`, then `lam M i ≤ Q · lam L i`.  (`Q ≥ 1`.) -/
private lemma lam_le_of_smul_mem {ι : Type*} [Fintype ι] (M L : Submodule ℤ (ι → ℤ)) (Q : ℕ)
    (hQ : 1 ≤ Q) (h : ∀ a ∈ L, (Q : ℤ) • a ∈ M) {i : ℕ} (hi : i ≤ rk L) :
    lam M i ≤ (Q : ℝ) * lam L i := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hQne : ((Q : ℤ)) ≠ 0 := by
    have h : (Q : ℕ) ≠ 0 := by omega
    exact_mod_cast h
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hεQ : 0 < ε / (Q : ℝ) := div_pos hε hQ0
  obtain ⟨r, hr, hrlt⟩ := exists_lt_of_csInf_lt (lamSet_nonempty L hi)
    (lt_add_of_pos_right _ hεQ)
  rw [← lam_eq_sInf] at hrlt
  obtain ⟨hr0, f, hfL, hfLI, hfr⟩ := hr
  have hker : (LinearMap.lsmul ℤ (ι → ℤ) (Q : ℤ)).ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    rw [LinearMap.mem_ker] at hz
    funext k
    have h1 : (Q : ℤ) • z = 0 := by simpa [LinearMap.lsmul_apply] using hz
    have hk : (Q : ℤ) • (z k) = 0 := by
      have := congrFun h1 k
      simpa using this
    have hk' : (Q : ℤ) * z k = 0 := by simpa [smul_eq_mul] using hk
    exact (mul_eq_zero.mp hk').resolve_left hQne
  have hLI : LinearIndependent ℤ (fun j => (Q : ℤ) • f j) := by
    have h2 : LinearIndependent ℤ
        (fun j => (LinearMap.lsmul ℤ (ι → ℤ) (Q : ℤ)) (f j)) :=
      hfLI.map (f := LinearMap.lsmul ℤ (ι → ℤ) (Q : ℤ))
        (by rw [hker]; exact disjoint_bot_right)
    simpa [LinearMap.lsmul_apply] using h2
  have hnorm : ∀ j, eNorm ((Q : ℤ) • f j) ≤ (Q : ℝ) * r := by
    intro j
    rw [MDEstimates.eNorm_smul_int]
    have hcast : ((((Q : ℤ)) : ℤ) : ℝ) = (Q : ℝ) := by push_cast; ring
    rw [hcast, abs_of_nonneg (le_of_lt hQ0)]
    exact mul_le_mul_of_nonneg_left (hfr j) (le_of_lt hQ0)
  have hmem : (Q : ℝ) * r ∈ lamSet M i :=
    ⟨mul_nonneg (le_of_lt hQ0) hr0, fun j => (Q : ℤ) • f j, fun j => h (f j) (hfL j), hLI, hnorm⟩
  have hle : lam M i ≤ (Q : ℝ) * r := by
    rw [lam_eq_sInf]
    exact csInf_le (bddBelow_lamSet M i) hmem
  have h2 : (Q : ℝ) * r < (Q : ℝ) * lam L i + ε := by
    calc (Q : ℝ) * r < (Q : ℝ) * (lam L i + ε / (Q : ℝ)) :=
          mul_lt_mul_of_pos_left hrlt hQ0
      _ = (Q : ℝ) * lam L i + ε := by
          rw [mul_add, mul_div_cancel₀ ε (ne_of_gt hQ0)]
  linarith

/-- (L0a) `GamMix(Q) ⊇ Q·Λ_{ν(x)}` has rank `N-1` and `λ_{N-1} ≤ Q λ(x)`. -/
theorem lam_GamMix_le (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (Q : ℕ) (hQ : 1 ≤ Q) :
    rk (GamMix d n x y Q) = NN d n - 1 ∧
      lam (GamMix d n x y Q) (NN d n - 1) ≤ (Q : ℝ) * lamX d n x := by
  have hd1 : 1 ≤ d := by omega
  have hu : IsPrim (veronese d n x) := isPrim_veronese d n hd1 hx
  have hne : veronese d n x ≠ 0 := by
    intro hzero
    have h0 : Finset.univ.gcd (veronese d n x) = 0 :=
      Finset.gcd_eq_zero_iff.mpr (fun m _ => by simpa using congrFun hzero m)
    rw [IsPrim] at hu
    rw [h0] at hu
    exact one_ne_zero hu.symm
  have hrankL : Module.finrank ℤ (latOrth (veronese d n x)) = NN d n - 1 := by
    rw [Vero.finrank_latOrth _ hne]
  have hrankM : rk (GamMix d n x y Q) = NN d n - 1 := by
    have h1 := (index_GamMix (veronese d n x) (veronese d n y) hu Q hQ).1
    rw [← GamMix] at h1
    exact h1.trans hrankL
  have hmem : ∀ a ∈ latOrth (veronese d n x), (Q : ℤ) • a ∈ GamMix d n x y Q := by
    intro a ha
    rw [GamMix, Submodule.mem_inf]
    refine ⟨Submodule.smul_mem _ (Q : ℤ) ha, ?_⟩
    rw [mem_latMod_iff, dotZ_smul]
    exact dvd_mul_right (Q : ℤ) _
  refine ⟨hrankM, ?_⟩
  have hbound : lam (GamMix d n x y Q) (NN d n - 1)
      ≤ (Q : ℝ) * lam (latOrth (veronese d n x)) (NN d n - 1) :=
    lam_le_of_smul_mem (GamMix d n x y Q) (latOrth (veronese d n x)) Q hQ hmem
      (i := NN d n - 1) (le_of_eq hrankL.symm)
  simpa [lamX] using hbound

end Work.HP.MM2

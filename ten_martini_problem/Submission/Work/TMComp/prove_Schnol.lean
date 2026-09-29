import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.Schnol.Defs
import Submission.Work.TMComp.Schnol.Basic
import Submission.Work.TMComp.Schnol.FiniteVolume
import Submission.Work.TMComp.Schnol.WindowSum
import Submission.Work.TMComp.Schnol.Select
import Submission.Work.TMComp.Schnol.Extract
import Submission.Work.TMC7Core.Scale.spectral_continuity

/-!
# Component C15 (`P_Schnol`): weak Schnol's theorem

Every point of the spectrum of an almost Mathieu operator is a limit of generalized
eigenvalues (Avila–Jitomirskaya, *The Ten Martini Problem*, §9 ¶1).

The proof is the finite-volume argument: take a finitely supported unit vector `ψ` with
`‖(H - E₀)ψ‖ < (δ/32)‖ψ‖` (`Work.TMC7Core.Scale.fs_approx`), normalise it to `φ`, restrict to
the window `[-M, M]` and use the eigen-decomposition of the Dirichlet truncation
(`winMat`) together with a pigeonhole argument to select an eigenvector whose zero extension
`u_M` solves the almost Mathieu equation on the window, satisfies `|u_M(m)| ≤ 1 + |m|`
everywhere, and has mass `≥ 1/(2*Wtot)` on the (fixed) support `s` of `φ`
(`Work.TMComp.Schnol.winMatSelect`).  A diagonal extraction
(`Work.TMComp.Schnol.subseqExtract`) produces a pointwise limit `u` and an energy limit `E`,
which solves the equation everywhere and is polynomially bounded.

The helper lemmas live in `Submission/Work/TMComp/Schnol/`.
-/

open scoped ENNReal
open Filter Topology
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp

theorem prove_Schnol : Work.TMContract.P_Schnol := by
  intro α lam θ H hH E₀ hE₀ δ hδ
  classical
  -- self-adjointness of the almost Mathieu operator
  have hsa : IsSelfAdjoint H := Schnol.selfAdjointAMO α lam θ hH
  -- the constants
  set ε : ℝ := δ / 8 with hεdef
  set η : ℝ := δ / 2 with hηdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hηpos : 0 < η := by rw [hηdef]; linarith
  have hεη : 4 * ε ^ 2 ≤ η ^ 2 := by rw [hεdef, hηdef]; nlinarith
  -- a finitely supported approximate eigenvector
  obtain ⟨ψ, hψne, ⟨s, hψs⟩, hψeig⟩ :=
    Work.TMC7Core.Scale.fs_approx H hsa E₀ hE₀ (δ := δ / 32) (by linarith)
  have hsub : ∀ w : EllTwo,
      (H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E₀) w = H w - (E₀ : ℂ) • w := by
    intro w
    rw [sub_apply, Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
  have hψeig' : ‖H ψ - (E₀ : ℂ) • ψ‖ < (δ / 32) * ‖ψ‖ := by
    rw [← hsub ψ]
    exact hψeig
  -- normalise
  set c₀ : ℝ := ‖ψ‖⁻¹ with hc₀def
  have hc₀pos : 0 < c₀ := by rw [hc₀def]; exact inv_pos.mpr (norm_pos_iff.mpr hψne)
  set φ : EllTwo := (c₀ : ℂ) • ψ with hφdef
  have hφnorm : ‖φ‖ = 1 := by
    rw [hφdef, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc₀pos, hc₀def,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hψne)]
  have hφsupp : ∀ n : ℤ, n ∉ s → φ n = 0 := by
    intro n hn
    rw [hφdef, lp.coeFn_smul, Pi.smul_apply, hψs n hn, smul_zero]
  have hφeig : ‖H φ - (E₀ : ℂ) • φ‖ ≤ ε := by
    have h1 : H φ - (E₀ : ℂ) • φ = (c₀ : ℂ) • (H ψ - (E₀ : ℂ) • ψ) := by
      rw [hφdef, map_smul, smul_sub, smul_smul, smul_smul, mul_comm (E₀ : ℂ) (c₀ : ℂ)]
    have h2 : ‖ψ‖⁻¹ * ‖H ψ - (E₀ : ℂ) • ψ‖ < ε := by
      have h3 : ‖ψ‖⁻¹ * ‖H ψ - (E₀ : ℂ) • ψ‖ < ‖ψ‖⁻¹ * ((δ / 32) * ‖ψ‖) :=
        mul_lt_mul_of_pos_left hψeig' (inv_pos.mpr (norm_pos_iff.mpr hψne))
      have h4 : ‖ψ‖⁻¹ * ((δ / 32) * ‖ψ‖) = δ / 32 := by
        field_simp
      rw [h4] at h3
      calc ‖ψ‖⁻¹ * ‖H ψ - (E₀ : ℂ) • ψ‖ < δ / 32 := h3
        _ ≤ ε := by rw [hεdef]; linarith
    rw [h1, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc₀pos, hc₀def]
    exact h2.le
  -- the (finite) support of `φ`
  set Y : ℕ := s.sup (fun n => n.natAbs) with hYdef
  have hsY : ∀ n ∈ s, -((Y : ℕ) : ℤ) ≤ n ∧ n ≤ ((Y : ℕ) : ℤ) := by
    intro n hn
    have h1 : n.natAbs ≤ Y := by
      rw [hYdef]
      exact Finset.le_sup hn
    have h2 : |n| ≤ ((Y : ℕ) : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h1
    exact abs_le.mp h2
  have hsuppY : ∀ n : ℤ, (n < -((Y : ℕ) : ℤ) ∨ ((Y : ℕ) : ℤ) < n) → φ n = 0 := by
    intro n hn
    apply hφsupp
    intro hmem
    rcases hn with h | h
    · exact absurd (hsY n hmem).1 (by omega)
    · exact absurd (hsY n hmem).2 (by omega)
  -- the finite-volume selection at every scale
  have hseq : ∀ k : ℕ, ∃ (E : ℝ) (u : ℤ → ℂ),
      |E - E₀| ≤ η ∧ (∀ m : ℤ, ‖u m‖ ≤ 1 + |(m : ℝ)|) ∧
      (1 / (2 * Schnol.Wtot)) ≤ ∑ m ∈ s, ‖u m‖ ^ 2 ∧
      (∀ m : ℤ, -(((k + Y + 1 : ℕ)) : ℤ) ≤ m → m ≤ (((k + Y + 1 : ℕ)) : ℤ) →
        Work.TMContract.amoAct α lam θ u m = (E : ℂ) * u m) ∧
      (∀ m : ℤ, (m < -(((k + Y + 1 : ℕ)) : ℤ) ∨ (((k + Y + 1 : ℕ)) : ℤ) < m) → u m = 0) := by
    intro k
    set M : ℕ := k + Y + 1 with hMdef
    have hMY : ((Y : ℕ) : ℤ) + 1 ≤ (M : ℤ) := by
      rw [hMdef]; push_cast; omega
    have htr := Schnol.truncNormEq M ((Y : ℕ) : ℤ) hMY α lam θ hH φ E₀ hsuppY
    have hXnorm : ‖Schnol.winVec M φ‖ = 1 := by
      rw [htr.1, hφnorm]
    have hXdef : ‖(Schnol.winMat M α lam θ).toEuclideanLin (Schnol.winVec M φ)
        - (E₀ : ℂ) • (Schnol.winVec M φ)‖ ≤ ε := by
      rw [htr.2]
      exact hφeig
    have hXsupp' : ∀ i : Fin (2 * M + 1), ((i : ℤ) - (M : ℤ)) ∉ s →
        (Schnol.winVec M φ).ofLp i = 0 := by
      intro i hi
      show φ ((i : ℤ) - (M : ℤ)) = 0
      exact hφsupp _ hi
    have hsM : ∀ m ∈ s, -(M : ℤ) ≤ m ∧ m ≤ (M : ℤ) := by
      intro m hm
      have h := hsY m hm
      constructor <;> omega
    exact Schnol.winMatSelect M α lam θ hsM (Schnol.winVec M φ) hXnorm hXsupp'
      hεpos.le hεη hηpos hXdef
  choose Eseq useq hP using hseq
  have hEbound : ∀ k : ℕ, |Eseq k - E₀| ≤ η := fun k => (hP k).1
  have hUbnd : ∀ k : ℕ, ∀ m : ℤ, ‖useq k m‖ ≤ 1 + |(m : ℝ)| := fun k => (hP k).2.1
  have hUmass : ∀ k : ℕ, (1 / (2 * Schnol.Wtot)) ≤ ∑ m ∈ s, ‖useq k m‖ ^ 2 :=
    fun k => (hP k).2.2.1
  have hUrec : ∀ k : ℕ, ∀ m : ℤ, -(((k + Y + 1 : ℕ)) : ℤ) ≤ m →
      m ≤ (((k + Y + 1 : ℕ)) : ℤ) →
      Work.TMContract.amoAct α lam θ (useq k) m = (Eseq k : ℂ) * useq k m :=
    fun k => (hP k).2.2.2.1
  have hUzero : ∀ k : ℕ, ∀ m : ℤ,
      (m < -(((k + Y + 1 : ℕ)) : ℤ) ∨ (((k + Y + 1 : ℕ)) : ℤ) < m) → useq k m = 0 :=
    fun k => (hP k).2.2.2.2
  -- the sequence of energies is bounded
  have hEbound' : ∀ k : ℕ, |Eseq k| ≤ |E₀| + η := by
    intro k
    have h := hEbound k
    rw [abs_le] at h ⊢
    constructor <;> linarith [h.1, h.2, le_abs_self E₀, neg_abs_le E₀]
  -- extract a convergent subsequence
  obtain ⟨φs, hφmono, E', hE'bound, u', hu'bound, hE'tend, hu'tend⟩ :=
    Schnol.subseqExtract Eseq (|E₀| + η) hEbound' useq (fun m : ℤ => 1 + |(m : ℝ)|)
      (fun m => by positivity) (fun k m => hUbnd k m)
  have hE'close : |E' - E₀| ≤ η := by
    have hcont : Continuous fun x : ℝ => |x - E₀| := by fun_prop
    have hclosed : IsClosed {x : ℝ | |x - E₀| ≤ η} := isClosed_le hcont continuous_const
    exact hclosed.mem_of_tendsto hE'tend (Eventually.of_forall fun k => hEbound (φs k))
  -- the mass of the limit does not vanish
  have hmass : (1 / (2 * Schnol.Wtot)) ≤ ∑ m ∈ s, ‖u' m‖ ^ 2 := by
    have htend : Filter.Tendsto (fun k => ∑ m ∈ s, ‖useq (φs k) m‖ ^ 2) Filter.atTop
        (nhds (∑ m ∈ s, ‖u' m‖ ^ 2)) := by
      refine Finset.induction_on s ?_ ?_
      · simp
      · intro a t hat ih
        simp only [Finset.sum_insert hat]
        exact (((hu'tend a).norm).pow 2).add ih
    have hclosed : IsClosed {x : ℝ | (1 / (2 * Schnol.Wtot)) ≤ x} :=
      isClosed_le continuous_const continuous_id
    exact hclosed.mem_of_tendsto htend (Eventually.of_forall fun k => hUmass (φs k))
  have hu'ne : u' ≠ 0 := by
    intro h0
    have hzero : (∑ m ∈ s, ‖u' m‖ ^ 2) = 0 := by
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [h0]
      simp
    have hpos : 0 < 1 / (2 * Schnol.Wtot) := by
      have := Schnol.Wtot_pos
      positivity
    linarith [hmass, hzero]
  -- the limit solves the equation at every site
  have heq : ∀ m : ℤ,
      Work.TMContract.amoAct α lam θ u' m = (E' : ℂ) * u' m := by
    intro m
    have hev : ∀ᶠ k in Filter.atTop,
        Work.TMContract.amoAct α lam θ (useq (φs k)) m = Eseq (φs k) * useq (φs k) m := by
      refine Filter.eventually_atTop.mpr ⟨m.natAbs, fun k hk => ?_⟩
      have hk' : m.natAbs ≤ φs k := le_trans hk (hφmono.id_le k)
      have h2 : m.natAbs ≤ φs k + Y + 1 := by omega
      have habs : |m| ≤ (((φs k + Y + 1 : ℕ)) : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast h2
      obtain ⟨h1, h2⟩ := abs_le.mp habs
      exact hUrec (φs k) m h1 h2
    have hleft : Filter.Tendsto (fun k => Work.TMContract.amoAct α lam θ (useq (φs k)) m)
        Filter.atTop (nhds (Work.TMContract.amoAct α lam θ u' m)) := by
      have hsum : Filter.Tendsto (fun k => useq (φs k) (m + 1) + useq (φs k) (m - 1)
          + ((Work.TMContract.amoPot α lam θ m : ℝ) : ℂ) * useq (φs k) m) Filter.atTop
          (nhds (u' (m + 1) + u' (m - 1)
            + ((Work.TMContract.amoPot α lam θ m : ℝ) : ℂ) * u' m)) :=
        ((hu'tend (m + 1)).add (hu'tend (m - 1))).add
          ((hu'tend m).const_mul ((Work.TMContract.amoPot α lam θ m : ℝ) : ℂ))
      simpa only [Work.TMContract.amoAct] using hsum
    have hE'tendC : Filter.Tendsto (fun k => ((Eseq (φs k) : ℝ) : ℂ)) Filter.atTop
        (nhds ((E' : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto E').comp hE'tend
    have hright : Filter.Tendsto (fun k => Eseq (φs k) * useq (φs k) m) Filter.atTop
        (nhds (E' * u' m)) := hE'tendC.mul (hu'tend m)
    exact tendsto_nhds_unique (hleft.congr' hev) hright
  refine ⟨E', ?_, u', hu'ne, heq, 1, fun n => ?_⟩
  · have hηδ : η < δ := by rw [hηdef]; linarith
    linarith [hE'close]
  · simpa using hu'bound n

end Work.TMComp

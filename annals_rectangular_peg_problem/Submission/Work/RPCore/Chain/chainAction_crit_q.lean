import Mathlib
import Submission.Work.RPCore.Chain.ChainDefs

/-!
# The `q`-equation of the critical-point condition for `chainAction`

`chainAction n W q P` is the discrete (broken-geodesic) action

`∑ j : Fin n, Pⱼ · (q_{j+1} - q_j) - ∑ j : Fin (n+1), W j (q_j, Pⱼ^{eff})`.

This file computes its directional derivative in a `q`-direction and extracts, from the
critical-point condition `fderiv (chainAction) (q, P) = 0`, the `q`-equation

`∂_q W k (q k, P_k^{eff}) = P_k^{prev} - P_k^{eff}`.
-/

namespace Work.RPCore.Chain

open Work.RPV

noncomputable section

/-- Directional derivative of `t ↦ chainAction n W (q + t • qf) P` at `0`. -/
private lemma chainAction_hasDerivAt_q (n : ℕ) (W : Fin (n + 1) → PS → ℝ)
    (hWd : ∀ j, Differentiable ℝ (W j)) (q qf : Fin (n + 1) → ℝ × ℝ) (P : Fin n → ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => chainAction n W (q + t • qf) P)
      ((∑ j : Fin n, ((P j).1 * ((qf j.succ).1 - (qf j.castSucc).1) +
          (P j).2 * ((qf j.succ).2 - (qf j.castSucc).2)))
       - ∑ j : Fin (n + 1), fderiv ℝ (W j) (q j, Peff n P j) (qf j, 0)) 0 := by
  have hc1 : ∀ i, HasDerivAt (fun t : ℝ => ((q + t • qf) i).1) ((qf i).1) 0 := by
    intro i
    have h : (fun t : ℝ => ((q + t • qf) i).1) = (fun t : ℝ => (q i).1 + t * (qf i).1) := by
      funext t; simp
    rw [h]
    simpa using (((hasDerivAt_id (0:ℝ)).mul_const ((qf i).1)).const_add ((q i).1))
  have hc2 : ∀ i, HasDerivAt (fun t : ℝ => ((q + t • qf) i).2) ((qf i).2) 0 := by
    intro i
    have h : (fun t : ℝ => ((q + t • qf) i).2) = (fun t : ℝ => (q i).2 + t * (qf i).2) := by
      funext t; simp
    rw [h]
    simpa using (((hasDerivAt_id (0:ℝ)).mul_const ((qf i).2)).const_add ((q i).2))
  have hK : HasDerivAt
      (fun t : ℝ => ∑ j : Fin n,
        ((P j).1 * (((q + t • qf) j.succ).1 - ((q + t • qf) j.castSucc).1) +
         (P j).2 * (((q + t • qf) j.succ).2 - ((q + t • qf) j.castSucc).2)))
      (∑ j : Fin n, ((P j).1 * ((qf j.succ).1 - (qf j.castSucc).1) +
          (P j).2 * ((qf j.succ).2 - (qf j.castSucc).2))) 0 := by
    refine HasDerivAt.fun_sum ?_
    intro j _
    have h1 := (hc1 j.succ).sub (hc1 j.castSucc)
    have h2 := (hc2 j.succ).sub (hc2 j.castSucc)
    have hh1 := HasDerivAt.const_mul ((P j).1) h1
    have hh2 := HasDerivAt.const_mul ((P j).2) h2
    convert hh1.add hh2 using 2
  have hline : ∀ i, HasDerivAt (fun t : ℝ => (q + t • qf) i) (qf i) 0 := by
    intro i
    have hh : HasDerivAt (fun t : ℝ => t • qf) qf 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).smul_const qf
    exact (hasDerivAt_pi.mp (hh.const_add q)) i
  have hU : HasDerivAt (fun t : ℝ => ∑ j : Fin (n + 1), W j ((q + t • qf) j, Peff n P j))
      (∑ j : Fin (n + 1), fderiv ℝ (W j) (q j, Peff n P j) (qf j, 0)) 0 := by
    refine HasDerivAt.fun_sum ?_
    intro j _
    have hcurve : HasDerivAt (fun t : ℝ => ((q + t • qf) j, Peff n P j)) (qf j, 0) 0 :=
      (hline j).prodMk (hasDerivAt_const (0:ℝ) (Peff n P j))
    have hfd : HasFDerivAt (W j) (fderiv ℝ (W j) (q j, Peff n P j)) (q j, Peff n P j) :=
      ((hWd j).differentiableAt).hasFDerivAt
    have hfd' : HasFDerivAt (W j) (fderiv ℝ (W j) (q j, Peff n P j))
        (((q + (0:ℝ) • qf) j, Peff n P j)) := by
      simpa using hfd
    have hh := hfd'.comp_hasDerivAt (0:ℝ) hcurve
    exact hh
  exact hK.sub hU

/-- Evaluation of the kinetic sum at a `q`-direction supported at one index. -/
private lemma kinetic_sum_eval (n : ℕ) (P : Fin n → ℝ × ℝ) (k : Fin (n + 1)) (d : ℝ × ℝ)
    (qf : Fin (n + 1) → ℝ × ℝ) (hqf : ∀ i, qf i = if i = k then d else 0) :
    (∑ j : Fin n, ((P j).1 * ((qf j.succ).1 - (qf j.castSucc).1) +
        (P j).2 * ((qf j.succ).2 - (qf j.castSucc).2)))
      = ((Pprev n P k).1 * d.1 + (Pprev n P k).2 * d.2)
        - ((Peff n P k).1 * d.1 + (Peff n P k).2 * d.2) := by
  have hS : (∑ j : Fin n, ((P j).1 * ((qf j.succ).1 - (qf j.castSucc).1) +
        (P j).2 * ((qf j.succ).2 - (qf j.castSucc).2)))
      = (∑ j : Fin n, ((P j).1 * (qf j.succ).1 + (P j).2 * (qf j.succ).2))
        - (∑ j : Fin n, ((P j).1 * (qf j.castSucc).1 + (P j).2 * (qf j.castSucc).2)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hS]
  congr 1
  · by_cases hk : 0 < (k:ℕ)
    · obtain ⟨j₀, hj₀, hsucc⟩ : ∃ j₀ : Fin n, Pprev n P k = P j₀ ∧ j₀.succ = k :=
        ⟨⟨(k:ℕ)-1, by omega⟩, Pprev_pos hk, by apply Fin.ext; simp; omega⟩
      rw [hj₀]
      have hA0 : (∑ j : Fin n, ((P j).1 * (qf j.succ).1 + (P j).2 * (qf j.succ).2))
          = (P j₀).1 * (qf j₀.succ).1 + (P j₀).2 * (qf j₀.succ).2 := by
        apply Finset.sum_eq_single j₀
        · intro b _ hb
          have hb' : ¬ (b.succ = k) := fun h => hb (Fin.succ_injective n (h.trans hsucc.symm))
          rw [hqf b.succ, ite_eq_right hb']
          norm_num
        · intro hh; exact absurd (Finset.mem_univ j₀) hh
      rw [hA0]
      have hqj₀ : qf j₀.succ = d := by rw [hsucc, hqf]; simp
      rw [hqj₀]
    · have hpp : Pprev n P k = 0 := by rw [Pprev]; rw [dite_eq_right hk]
      rw [hpp]
      have hz : (∑ j : Fin n, ((P j).1 * (qf j.succ).1 + (P j).2 * (qf j.succ).2)) = 0 := by
        apply Finset.sum_eq_zero
        intro b _
        have hb' : ¬ (b.succ = k) := by
          intro h
          have h2 : (b.succ : ℕ) = (k:ℕ) := by rw [h]
          simp only [Fin.val_succ] at h2
          omega
        rw [hqf b.succ, ite_eq_right hb']
        norm_num
      rw [hz]; norm_num
  · by_cases hk : (k:ℕ) < n
    · obtain ⟨i₀, hi₀, hcast⟩ : ∃ i₀ : Fin n, Peff n P k = P i₀ ∧ i₀.castSucc = k :=
        ⟨⟨(k:ℕ), hk⟩, Peff_lt hk, by apply Fin.ext; simp⟩
      rw [hi₀]
      have hB0 : (∑ j : Fin n, ((P j).1 * (qf j.castSucc).1 + (P j).2 * (qf j.castSucc).2))
          = (P i₀).1 * (qf i₀.castSucc).1 + (P i₀).2 * (qf i₀.castSucc).2 := by
        apply Finset.sum_eq_single i₀
        · intro b _ hb
          have hb' : ¬ (b.castSucc = k) :=
            fun h => hb (Fin.castSucc_injective n (h.trans hcast.symm))
          rw [hqf b.castSucc, ite_eq_right hb']
          norm_num
        · intro hh; exact absurd (Finset.mem_univ i₀) hh
      rw [hB0]
      have hqi₀ : qf i₀.castSucc = d := by rw [hcast, hqf]; simp
      rw [hqi₀]
    · have hpe : Peff n P k = 0 := by rw [Peff]; rw [dite_eq_right hk]
      rw [hpe]
      have hz : (∑ j : Fin n, ((P j).1 * (qf j.castSucc).1 + (P j).2 * (qf j.castSucc).2)) = 0 := by
        apply Finset.sum_eq_zero
        intro b _
        have hb' : ¬ (b.castSucc = k) := by
          intro h
          have h2 : (b.castSucc : ℕ) = (k:ℕ) := by rw [h]
          simp only [Fin.val_castSucc] at h2
          omega
        rw [hqf b.castSucc, ite_eq_right hb']
        norm_num
      rw [hz]; norm_num

/-- Evaluation of the momentum sum at a `q`-direction supported at one index. -/
private lemma pot_sum_eval (n : ℕ) (W : Fin (n + 1) → PS → ℝ) (q : Fin (n + 1) → ℝ × ℝ)
    (P : Fin n → ℝ × ℝ) (k : Fin (n + 1)) (d : ℝ × ℝ) :
    (∑ j : Fin (n + 1), fderiv ℝ (W j) (q j, Peff n P j) ((if j = k then d else 0), 0))
      = fderiv ℝ (W k) (q k, Peff n P k) (d, 0) := by
  have hsum : (∑ j : Fin (n + 1), fderiv ℝ (W j) (q j, Peff n P j)
        ((if j = k then d else 0), 0))
      = fderiv ℝ (W k) (q k, Peff n P k) ((if k = k then d else 0), 0) := by
    apply Finset.sum_eq_single k
    · intro b _ hb
      rw [ite_eq_right hb]
      exact map_zero _
    · intro hh; exact absurd (Finset.mem_univ k) hh
  simpa using hsum

/-- The directional derivative of `chainAction`, as a function of `(q, P)`, along the direction
`(qf, 0)`. -/
private lemma chainAction_fderiv_dir (n : ℕ) (W : Fin (n + 1) → PS → ℝ)
    (hWd : ∀ j, Differentiable ℝ (W j)) (q qf : Fin (n + 1) → ℝ × ℝ) (P : Fin n → ℝ × ℝ) :
    ((fderiv ℝ (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
        chainAction n W z.1 z.2) (q, P)) (qf, 0))
      = (∑ j : Fin n, ((P j).1 * ((qf j.succ).1 - (qf j.castSucc).1) +
          (P j).2 * ((qf j.succ).2 - (qf j.castSucc).2)))
        - ∑ j : Fin (n + 1), fderiv ℝ (W j) (q j, Peff n P j) (qf j, 0) := by
  have hpath := chainAction_hasDerivAt_q n W hWd q qf P
  have hline : HasDerivAt (fun t : ℝ => (q + t • qf, P)) (qf, 0) 0 := by
    have hh : HasDerivAt (fun t : ℝ => t • qf) qf 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).smul_const qf
    have h1 : HasDerivAt (fun t : ℝ => q + t • qf) qf 0 := hh.const_add q
    exact h1.prodMk (hasDerivAt_const (0:ℝ) P)
  have hFd : HasFDerivAt (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
      chainAction n W z.1 z.2)
      (fderiv ℝ (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
        chainAction n W z.1 z.2) (q, P)) (q, P) :=
    (differentiableAt_chainAction n W hWd q P).hasFDerivAt
  have hFd' : HasFDerivAt (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
      chainAction n W z.1 z.2)
      (fderiv ℝ (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
        chainAction n W z.1 z.2) (q, P)) (q + (0:ℝ) • qf, P) := by
    simpa using hFd
  have hcomp : HasDerivAt (fun t : ℝ => chainAction n W (q + t • qf) P)
      ((fderiv ℝ (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
        chainAction n W z.1 z.2) (q, P)) (qf, 0)) 0 :=
    HasFDerivAt.comp_hasDerivAt
      (l := fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) => chainAction n W z.1 z.2)
      (0 : ℝ) hFd' hline
  exact hcomp.unique hpath

theorem chainAction_crit_q (n : ℕ) (W : Fin (n + 1) → Work.RPV.PS → ℝ)
    (hWd : ∀ j, Differentiable ℝ (W j)) (q : Fin (n + 1) → ℝ × ℝ) (P : Fin n → ℝ × ℝ)
    (hcrit : fderiv ℝ (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
      Work.RPV.chainAction n W z.1 z.2) (q, P) = 0) :
    ∀ k : Fin (n + 1),
      Work.RPV.dq (W k) (q k) (Work.RPCore.Chain.Peff n P k)
        = Work.RPCore.Chain.Pprev n P k - Work.RPCore.Chain.Peff n P k := by
  intro k
  have hkey : ∀ d : ℝ × ℝ,
      fderiv ℝ (W k) (q k, Peff n P k) (d, ((0:ℝ),(0:ℝ)))
        = ((Pprev n P k).1 * d.1 + (Pprev n P k).2 * d.2)
          - ((Peff n P k).1 * d.1 + (Peff n P k).2 * d.2) := by
    intro d
    let qf : Fin (n + 1) → ℝ × ℝ := fun i => if i = k then d else 0
    have hqf : ∀ i, qf i = if i = k then d else 0 := fun i => rfl
    have hdir := chainAction_fderiv_dir n W hWd q qf P
    have hzero : (∑ j : Fin n, ((P j).1 * ((qf j.succ).1 - (qf j.castSucc).1) +
          (P j).2 * ((qf j.succ).2 - (qf j.castSucc).2)))
        - ∑ j : Fin (n + 1), fderiv ℝ (W j) (q j, Peff n P j) (qf j, 0) = 0 := by
      rw [← hdir, hcrit]
      simp
    have hS := kinetic_sum_eval n P k d qf hqf
    have hT := pot_sum_eval n W q P k d
    have heq : (∑ j : Fin (n + 1), fderiv ℝ (W j) (q j, Peff n P j) (qf j, 0))
        = (∑ j : Fin n, ((P j).1 * ((qf j.succ).1 - (qf j.castSucc).1) +
            (P j).2 * ((qf j.succ).2 - (qf j.castSucc).2))) := (sub_eq_zero.mp hzero).symm
    calc fderiv ℝ (W k) (q k, Peff n P k) (d, 0)
        = (∑ j : Fin (n + 1), fderiv ℝ (W j) (q j, Peff n P j) (qf j, 0)) := hT.symm
      _ = (∑ j : Fin n, ((P j).1 * ((qf j.succ).1 - (qf j.castSucc).1) +
            (P j).2 * ((qf j.succ).2 - (qf j.castSucc).2))) := heq
      _ = ((Pprev n P k).1 * d.1 + (Pprev n P k).2 * d.2)
            - ((Peff n P k).1 * d.1 + (Peff n P k).2 * d.2) := hS
  have h1 : (fderiv ℝ (W k) (q k, Peff n P k)) ((1, 0), (0, 0))
      = (Pprev n P k).1 - (Peff n P k).1 := by
    rw [hkey ((1 : ℝ), (0 : ℝ))]
    ring
  have h2 : (fderiv ℝ (W k) (q k, Peff n P k)) ((0, 1), (0, 0))
      = (Pprev n P k).2 - (Peff n P k).2 := by
    rw [hkey ((0 : ℝ), (1 : ℝ))]
    ring
  refine Prod.ext ?_ ?_
  · show (fderiv ℝ (W k) (q k, Peff n P k)) ((1, 0), (0, 0))
        = (Pprev n P k).1 - (Peff n P k).1
    exact h1
  · show (fderiv ℝ (W k) (q k, Peff n P k)) ((0, 1), (0, 0))
        = (Pprev n P k).2 - (Peff n P k).2
    exact h2

end

end Work.RPCore.Chain

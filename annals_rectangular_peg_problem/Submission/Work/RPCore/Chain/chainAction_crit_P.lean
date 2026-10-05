import Mathlib
import Submission.Work.RPCore.Chain.ChainDefs

namespace Work.RPCore.Chain

open Work.RPV

/-- Directional derivative of the chain action in the direction of the `P`-variables.

The `P`-dependence of `chainAction n W q P'` is: linear with slope `q (j+1) - q j` in the
component `P' j`, plus the dependence through the second slot `P' j` of `W j.castSucc`.
Hence the derivative of `t ↦ chainAction n W q (P + t • v)` at `t = 0` is
`∑ j, v j · (q (j+1) - q j) - ∑ j, ∂_P W j.castSucc (q j, P j) (v j)`. -/
lemma hasDerivAt_chainAction_along_P (n : ℕ) (W : Fin (n + 1) → PS → ℝ)
    (hWd : ∀ j, Differentiable ℝ (W j)) (q : Fin (n + 1) → ℝ × ℝ) (P : Fin n → ℝ × ℝ)
    (v : Fin n → ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => chainAction n W q (P + t • v))
      ((∑ j : Fin n, ((v j).1 * ((q j.succ).1 - (q j.castSucc).1) +
        (v j).2 * ((q j.succ).2 - (q j.castSucc).2)))
        - ∑ j : Fin n, fderiv ℝ (W j.castSucc) (q j.castSucc, P j) (0, v j)) 0 := by
  -- the linear part of the chain action
  have hlin : HasDerivAt (∑ j : Fin n, fun t : ℝ =>
      (((P + t • v) j).1 * ((q j.succ).1 - (q j.castSucc).1) +
       ((P + t • v) j).2 * ((q j.succ).2 - (q j.castSucc).2)))
      (∑ j : Fin n, ((v j).1 * ((q j.succ).1 - (q j.castSucc).1) +
       (v j).2 * ((q j.succ).2 - (q j.castSucc).2))) 0 := by
    apply HasDerivAt.sum
    intro j _
    have ha : HasDerivAt (fun t : ℝ => (P j).1 + t * (v j).1) ((v j).1) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const ((v j).1)).const_add ((P j).1)
    have hb : HasDerivAt (fun t : ℝ => (P j).2 + t * (v j).2) ((v j).2) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const ((v j).2)).const_add ((P j).2)
    have h := (ha.mul_const ((q j.succ).1 - (q j.castSucc).1)).add
      (hb.mul_const ((q j.succ).2 - (q j.castSucc).2))
    convert h using 1
  -- the part coming from the generating functions; only the `j < n` slots depend on `P`
  have hWsum : HasDerivAt (fun t : ℝ => ∑ k : Fin (n + 1), W k (q k, Peff n (P + t • v) k))
      (∑ j : Fin n, fderiv ℝ (W j.castSucc) (q j.castSucc, P j) (0, v j)) 0 := by
    have hfun : (fun t : ℝ => ∑ k : Fin (n + 1), W k (q k, Peff n (P + t • v) k))
        = (fun t : ℝ => (∑ j : Fin n, W j.castSucc (q j.castSucc, (P + t • v) j))
            + W (Fin.last n) (q (Fin.last n), 0)) := by
      funext t
      rw [Fin.sum_univ_castSucc]
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        rw [Peff_castSucc]
      · rw [Peff_last]
    rw [hfun]
    have h1 : HasDerivAt (fun t : ℝ => ∑ j : Fin n, W j.castSucc (q j.castSucc, (P + t • v) j))
        (∑ j : Fin n, fderiv ℝ (W j.castSucc) (q j.castSucc, P j) (0, v j)) 0 := by
      have h : HasDerivAt (∑ j : Fin n, fun t : ℝ => W j.castSucc (q j.castSucc, (P + t • v) j))
          (∑ j : Fin n, fderiv ℝ (W j.castSucc) (q j.castSucc, P j) (0, v j)) 0 := by
        apply HasDerivAt.sum
        intro j _
        have hcurve : HasDerivAt (fun t : ℝ => (q j.castSucc, (P + t • v) j)) (0, v j) 0 := by
          have h1 : HasDerivAt (fun t : ℝ => (P + t • v) j) (v j) 0 := by
            simpa using ((hasDerivAt_id (0:ℝ)).smul_const (v j)).const_add (P j)
          exact (hasDerivAt_const (0:ℝ) (q j.castSucc)).prodMk h1
        have hW : HasFDerivAt (W j.castSucc)
            (fderiv ℝ (W j.castSucc) (q j.castSucc, (P + (0:ℝ) • v) j))
            (q j.castSucc, (P + (0:ℝ) • v) j) :=
          ((hWd j.castSucc).differentiableAt
            (x := (q j.castSucc, (P + (0:ℝ) • v) j))).hasFDerivAt
        convert hW.comp_hasDerivAt 0 hcurve using 1
        · rfl
        · simp
      convert h using 1
      ext t
      simp [Finset.sum_apply]
    have h2 : HasDerivAt (fun t : ℝ => W (Fin.last n) (q (Fin.last n), 0)) 0 0 :=
      hasDerivAt_const 0 _
    have h3 := h1.add h2
    convert h3 using 1
    rw [add_zero]
  -- combine
  have h := hlin.sub hWsum
  convert h using 1
  · ext t
    simp only [chainAction, Peff, Pi.sub_apply, Finset.sum_apply]

theorem chainAction_crit_P (n : ℕ) (W : Fin (n + 1) → Work.RPV.PS → ℝ)
    (hWd : ∀ j, Differentiable ℝ (W j)) (q : Fin (n + 1) → ℝ × ℝ) (P : Fin n → ℝ × ℝ)
    (hcrit : fderiv ℝ (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
      Work.RPV.chainAction n W z.1 z.2) (q, P) = 0) :
    ∀ j : Fin n,
      q j.succ - q j.castSucc = Work.RPV.dP (W j.castSucc) (q j.castSucc)
        (Work.RPCore.Chain.Peff n P j.castSucc) := by
  -- criticality of the full chain action gives vanishing directional derivative in the
  -- `P`-directions
  have dirCrit : ∀ v : Fin n → ℝ × ℝ,
      HasDerivAt (fun t : ℝ => chainAction n W q (P + t • v)) 0 0 := by
    intro v
    have hcurve : HasDerivAt (fun t : ℝ => (q, P + t • v)) (0, v) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => P + t • v) v 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add P
      exact (hasDerivAt_const (0:ℝ) q).prodMk h1
    have hF : HasFDerivAt (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
        chainAction n W z.1 z.2)
        (0 : ((Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ)) →L[ℝ] ℝ)
        (q, P + (0:ℝ) • v) := by
      have h0 := (differentiableAt_chainAction n W hWd q (P + (0:ℝ) • v)).hasFDerivAt
      have hd : fderiv ℝ (fun z : (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
          chainAction n W z.1 z.2) (q, P + (0:ℝ) • v) = 0 := by
        have hpt : (q, P + (0:ℝ) • v) = (q, P) := by simp
        rw [hpt, hcrit]
      rw [hd] at h0
      exact h0
    have h := hF.comp_hasDerivAt 0 hcurve
    convert h using 1
    · ext t
      rfl
  -- the explicit directional derivative is therefore zero
  have key : ∀ v : Fin n → ℝ × ℝ,
      (∑ j : Fin n, ((v j).1 * ((q j.succ).1 - (q j.castSucc).1) +
        (v j).2 * ((q j.succ).2 - (q j.castSucc).2)))
        - ∑ j : Fin n, fderiv ℝ (W j.castSucc) (q j.castSucc, P j) (0, v j) = 0 :=
    fun v => (hasDerivAt_chainAction_along_P n W hWd q P v).unique (dirCrit v)
  -- evaluate on the coordinate directions
  have key' : ∀ (j : Fin n) (a : ℝ × ℝ),
      ((a).1 * ((q j.succ).1 - (q j.castSucc).1) + (a).2 * ((q j.succ).2 - (q j.castSucc).2))
        - fderiv ℝ (W j.castSucc) (q j.castSucc, P j) (0, a) = 0 := by
    intro j a
    have h := key (fun k => if k = j then a else 0)
    have hs1 : (∑ k : Fin n, (((fun k => if k = j then a else 0) k).1 *
        ((q k.succ).1 - (q k.castSucc).1) +
        (((fun k => if k = j then a else 0) k)).2 * ((q k.succ).2 - (q k.castSucc).2)))
        = ((a).1 * ((q j.succ).1 - (q j.castSucc).1) +
            (a).2 * ((q j.succ).2 - (q j.castSucc).2)) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk; simp [hk]
      · intro hmem; exact absurd (Finset.mem_univ j) hmem
    have hs2 : (∑ k : Fin n, fderiv ℝ (W k.castSucc) (q k.castSucc, P k)
        (0, (fun k => if k = j then a else 0) k))
        = fderiv ℝ (W j.castSucc) (q j.castSucc, P j) (0, a) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        simp only [hk]
        exact ContinuousLinearMap.map_zero _
      · intro hmem; exact absurd (Finset.mem_univ j) hmem
    rw [hs1, hs2] at h
    exact h
  intro j
  rw [Peff_castSucc]
  have h1 := key' j ((1 : ℝ), 0)
  have h2 := key' j (0, (1 : ℝ))
  simp only [one_mul, zero_mul, zero_add, add_zero, sub_eq_zero] at h1 h2
  rw [dP]
  ext <;> simp only [Prod.fst_sub, Prod.snd_sub]
  · exact h1
  · exact h2

end Work.RPCore.Chain

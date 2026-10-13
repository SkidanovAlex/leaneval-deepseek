import Mathlib

namespace Work.WilkiesH.Interp

open Set Filter
open scoped Topology

/-- Chain rule for the iterated Fréchet derivative along the line `s ↦ x + s • v`.

If `F` is `C^n` on the open set `U` and the point `x + t • v` lies in `U`, then the `i`-th
iterated derivative of `s ↦ F (x + s • v)` at `t` is obtained from the `i`-th iterated
derivative of `F` at `x + t • v` by composing each of the `i` multilinear slots with the
linear map `s ↦ s • v`. -/
theorem iteratedFDerivAlongLine {m n : ℕ} {F : (Fin m → ℝ) → ℝ} {U : Set (Fin m → ℝ)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ (n : ℕ) F U)
    {x v : Fin m → ℝ} {i : ℕ} (hi : i ≤ n) {t : ℝ} (ht : x + t • v ∈ U) :
    iteratedFDeriv ℝ i (fun s : ℝ => F (x + s • v)) t =
      (iteratedFDeriv ℝ i F (x + t • v)).compContinuousLinearMap
        (fun _ : Fin i => ContinuousLinearMap.toSpanSingleton ℝ v) := by
  set L : ℝ →L[ℝ] (Fin m → ℝ) := (ContinuousLinearMap.toSpanSingleton ℝ v) with hL
  have hLapply : ∀ s : ℝ, L s = s • v := fun s => by
    rw [hL]; exact ContinuousLinearMap.toSpanSingleton_apply ℝ v s
  set U' : Set (Fin m → ℝ) := (fun z : Fin m → ℝ => x + z) ⁻¹' U with hU'def
  have hU'open : IsOpen U' := hU.preimage (by fun_prop)
  have hSopen : IsOpen (L ⁻¹' U') := hU'open.preimage L.continuous
  have ht' : L t ∈ U' := by rw [hU'def, Set.mem_preimage, hLapply]; exact ht
  have htS : t ∈ L ⁻¹' U' := ht'
  have hFx : ContDiffOn ℝ (n : ℕ) (fun z : Fin m → ℝ => F (x + z)) U' :=
    hF.comp (by fun_prop) (fun z hz => hz)
  have hcomp := L.iteratedFDerivWithin_comp_right hFx hU'open.uniqueDiffOn
      hSopen.uniqueDiffOn ht' (by exact_mod_cast hi)
  have hEvS : (L ⁻¹' U') =ᶠ[𝓝 t] univ := by
    filter_upwards [hSopen.mem_nhds htS] with y hy
    simp [hy]
  have hEvU : U' =ᶠ[𝓝 (L t)] univ := by
    filter_upwards [hU'open.mem_nhds ht'] with y hy
    simp [hy]
  have hleft : iteratedFDerivWithin ℝ i ((fun z : Fin m → ℝ => F (x + z)) ∘ L) (L ⁻¹' U') t
      = iteratedFDeriv ℝ i (fun s : ℝ => F (x + s • v)) t := by
    rw [iteratedFDerivWithin_congr_set hEvS i, iteratedFDerivWithin_univ]
    congr 1
  have hright : (iteratedFDerivWithin ℝ i (fun z : Fin m → ℝ => F (x + z)) U' (L t))
      = iteratedFDeriv ℝ i F (x + t • v) := by
    rw [iteratedFDerivWithin_congr_set hEvU i, iteratedFDerivWithin_univ,
        iteratedFDeriv_comp_add_left]
    rw [hLapply]
  rw [← hleft, hcomp, hright, hL]

/-- Taylor's theorem with a sharp remainder bound along the segment from `x` to `y`.

Let `U` be open and convex, `F : ℝ^m → ℝ` be `C^{b+1}` on `U`, and `x, y ∈ U`.  If all
iterated derivatives of `F` at `x` of order `≤ b` vanish and the `(b+1)`-st iterated
derivative of `F` is bounded by `C` on the segment `[x, y]`, then
`|F y| ≤ C / (b+1)! * ‖y - x‖^{b+1}`. -/
theorem taylor_diag_bound {m b : ℕ} {F : (Fin m → ℝ) → ℝ} {U : Set (Fin m → ℝ)}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hF : ContDiffOn ℝ (b + 1 : ℕ) F U)
    {x y : Fin m → ℝ} (hx : x ∈ U) (hy : y ∈ U)
    (hjet : ∀ j ≤ b, iteratedFDeriv ℝ j F x = 0) {C : ℝ}
    (hC : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (b + 1) F (x + s • (y - x))‖ ≤ C) :
    |F y| ≤ C / ((b + 1).factorial : ℝ) * ‖y - x‖ ^ (b + 1) := by
  set v : Fin m → ℝ := y - x with hv
  set g : ℝ → ℝ := fun s => F (x + s • v) with hg
  have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le (by norm_num)
  -- the segment from `x` to `y` lies in `U` (convexity)
  have hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, x + s • v ∈ U := by
    intro s hs
    have hmem : (1 - s) • x + s • y ∈ U :=
      (hconv.starConvex hx) hy (by linarith [hs.2]) hs.1 (by ring)
    have heq : x + s • v = (1 - s) • x + s • y := by
      rw [hv, smul_sub, sub_smul, one_smul]; abel
    rw [heq]; exact hmem
  -- smoothness of the parametrised curve
  have hGS : ContDiffOn ℝ (b + 1 : ℕ) g ((fun s : ℝ => x + s • v) ⁻¹' U) := by
    rw [hg]; exact hF.comp (by fun_prop) (fun s hs => hs)
  have hPathOn : ContDiffOn ℝ (b + 1 : ℕ) g (Set.uIcc (0 : ℝ) 1) := by
    rw [huIcc]; exact hGS.mono (fun s hs => hseg s hs)
  have hSopen : IsOpen ((fun s : ℝ => x + s • v) ⁻¹' U) := hU.preimage (by fun_prop)
  have h0S : (0 : ℝ) ∈ (fun s : ℝ => x + s • v) ⁻¹' U := by simpa using hx
  have hGAt : ContDiffAt ℝ (b + 1 : ℕ) g 0 := hGS.contDiffAt (hSopen.mem_nhds h0S)
  -- all derivatives of `g` at `0` of order `≤ b` vanish
  have hzero : ∀ k ≤ b, iteratedDerivWithin k g (Set.uIcc (0 : ℝ) 1) 0 = 0 := by
    intro k hk
    have hcd : ContDiffAt ℝ (k : ℕ) g 0 := hGAt.of_le (by exact_mod_cast (by omega : k ≤ b + 1))
    rw [huIcc]
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) hcd
      ⟨le_refl 0, by norm_num⟩]
    rw [hg]
    show (iteratedFDeriv ℝ k (fun s : ℝ => F (x + s • v)) 0) (fun _ => (1 : ℝ)) = 0
    rw [iteratedFDerivAlongLine (n := b + 1) hU hF (i := k) (by omega) (t := 0)
      (by simpa using hx)]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      show x + (0 : ℝ) • v = x from by simp, hjet k hk]
    simp
  -- Taylor's theorem with the Lagrange form of the remainder
  obtain ⟨ξ, hξ, hξeq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := g)
    (x := (1 : ℝ)) (x₀ := 0) (n := b) (by norm_num) hPathOn
  have hξI : ξ ∈ Set.Icc (0 : ℝ) 1 := by
    have h := hξ
    rw [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hTay0 : taylorWithinEval g b (Set.uIcc (0 : ℝ) 1) 0 1 = 0 := by
    rw [taylor_within_apply]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [hzero k (by omega), smul_zero]
  have hg1 : g 1 = iteratedDeriv (b + 1) g ξ / ((b + 1).factorial : ℝ) := by
    have h := hξeq
    rw [hTay0, sub_zero, sub_zero, one_pow, mul_one] at h
    exact h
  have hg1F : g 1 = F y := by
    rw [hg]
    simp only [one_smul]
    rw [hv]
    simp
  have hFy : F y = iteratedDeriv (b + 1) g ξ / ((b + 1).factorial : ℝ) := by
    rw [← hg1F, hg1]
  -- bound on the last derivative of `g`
  have hbound : ‖iteratedDeriv (b + 1) g ξ‖ ≤ C * ‖v‖ ^ (b + 1) := by
    have hξU : x + ξ • v ∈ U := hseg ξ hξI
    have hchain := iteratedFDerivAlongLine (n := b + 1) hU hF (i := b + 1) le_rfl (t := ξ) hξU
    have hA : ‖iteratedDeriv (b + 1) g ξ‖
        = ‖(iteratedFDeriv ℝ (b + 1) F (x + ξ • v)) (fun _ : Fin (b + 1) => v)‖ := by
      rw [iteratedDeriv, hg]
      rw [hchain, ContinuousMultilinearMap.compContinuousLinearMap_apply]
      simp [ContinuousLinearMap.toSpanSingleton_apply]
    refine hA.trans_le ?_
    calc ‖(iteratedFDeriv ℝ (b + 1) F (x + ξ • v)) (fun _ : Fin (b + 1) => v)‖
        ≤ ‖iteratedFDeriv ℝ (b + 1) F (x + ξ • v)‖ * (∏ _ : Fin (b + 1), ‖v‖) :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ (b + 1) F (x + ξ • v)‖ * ‖v‖ ^ (b + 1) := by
          simp [Finset.prod_const]
      _ ≤ C * ‖v‖ ^ (b + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact hC ξ hξI
  rw [hFy]
  have hfact : (0 : ℝ) < ((b + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (b + 1)
  rw [abs_div, abs_of_pos hfact, ← Real.norm_eq_abs]
  refine (div_le_div_of_nonneg_right hbound hfact.le).trans (le_of_eq ?_)
  ring

end Work.WilkiesH.Interp

import Mathlib
import Submission.Work.Drive.Rays.rayStraighteningTarget
import Submission.Work.Drive.exists_reparamLand
import Submission.Work.Drive.TwoRays.stageReparam

namespace Work.Drive

/-!  The strengthening of `Work.Drive.clipArc` by the row `P '' Icc 0 1 ⊆ α '' Icc 0 1`
(the clipped piece stays inside the original arc's image on `[0,1]`), which is what makes the
"last visit of `ρ` to the image" invariant pass from `α` to `P`.  The recipe and all the rows are
those of `Work.Drive.clipArc` (`Submission/Work/Drive/clipArc.lean`): take `ψ` from
`Work.Drive.exists_reparamLand`, put `P := α ∘ ψ`; the extra row follows from
`ψ t ∈ Set.Icc 0 s` for `t ∈ Set.Icc 0 1` (the brick's row `ψ ≤ s`, monotonicity and `ψ 0 = 0`). -/
theorem clipArcImage {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M] [SecondCountableTopology M]
    {α : ℝ → M} (hαsm : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) Work.Noncompact.CompressionTube.smoothOrder α)
    (hαimm : ∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) α t))
    (hαinj : Set.InjOn α (Set.Icc (0:ℝ) 1))
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hger : ∀ t : ℝ, 0 ≤ t → t ≤ ε → α t = c.symm (c (α 0) + t • v))
    (htgt : ∀ t : ℝ, 0 ≤ t → t ≤ ε → c (α 0) + t • v ∈ c.target)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∃ (P : ℝ → M) (e' : ℝ) (c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (w' : EuclideanSpace ℝ (Fin n)) (eout : ℝ),
      P 0 = α 0 ∧ P 1 = α s ∧ P '' Set.Icc (0:ℝ) 1 ⊆ α '' Set.Icc (0:ℝ) 1 ∧
      ContMDiff Work.Noncompact.CompressionTube.MCreal (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder P ∧
      (∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) P t)) ∧
      Set.InjOn P (Set.Icc (0:ℝ) 1) ∧
      0 < e' ∧ (∀ t : ℝ, 0 ≤ t → t ≤ e' → P t = c.symm (c (α 0) + t • v)) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e' → c (α 0) + t • v ∈ c.target) ∧
      0 < eout ∧ w' ≠ 0 ∧ c' ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder M ∧ α s ∈ c'.source ∧
      (∀ t : ℝ, 1 - eout ≤ t → t ≤ 1 → P t = c'.symm (c' (α s) + (t - 1) • w')) ∧
      (∀ t : ℝ, 1 - eout ≤ t → t ≤ 1 → c' (α s) + (t - 1) • w' ∈ c'.target) := by
  -- the clip extent
  set ee : ℝ := min (ε / 2) (min (s / 2) (1 / 4)) with hee
  have hee_pos : 0 < ee := by
    rw [hee]; exact lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have hee_lt_half : ee < 1 / 2 := by
    have h : ee ≤ 1 / 4 := by
      rw [hee]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have hee_lt_s : ee < s := by
    have h : ee ≤ s / 2 := by
      rw [hee]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hee_le_eps : ee ≤ ε := by
    have h : ee ≤ ε / 2 := by rw [hee]; exact min_le_left _ _
    linarith
  obtain ⟨ψ, hψsm, hψder, hψid, hψ1, hψle, μ, a, hμpos, ha1, hψaff⟩ :=
    exists_reparamLand (e := ee) (s := s) hee_pos hee_lt_half hee_lt_s
  have hψcmd : ContMDiff Work.Noncompact.CompressionTube.MCreal
      Work.Noncompact.CompressionTube.MCreal Work.Noncompact.CompressionTube.smoothOrder ψ :=
    hψsm.contMDiff
  have hstrict : ∀ t : ℝ, HasStrictDerivAt ψ (deriv ψ t) t :=
    fun t => hψsm.hasStrictDerivAt (by simp)
  have hmd : ∀ t : ℝ, MDifferentiableAt Work.Noncompact.CompressionTube.MCreal
      Work.Noncompact.CompressionTube.MCreal ψ t :=
    fun t => hψcmd.contMDiffAt.mdifferentiableAt (by simp)
  have hmono : StrictMono ψ := strictMono_of_deriv_pos hψder
  have hψ0 : ψ 0 = 0 := hψid 0 hee_pos.le
  have hψnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ ψ t := by
    intro t ht
    simpa [hψ0] using hmono.monotone ht
  -- terminal straightening of `α` at `s`
  obtain ⟨c₂, w₂, e₂, hw₂, he₂, hc₂, hsrc₂, htgt₂, hger₂⟩ :=
    Rays.rayStraightening_target (n := n) (M := M) hn hαsm.contMDiffOn
      (fun t _ => hαimm t) hs0.le
  -- the terminal extent
  set eo : ℝ := min (1 - a) (min (s / μ) (e₂ / μ)) with heo
  have heo_pos : 0 < eo := by
    rw [heo]
    exact lt_min (by linarith) (lt_min (div_pos hs0 hμpos) (div_pos he₂ hμpos))
  have heo_a : eo ≤ 1 - a := by rw [heo]; exact min_le_left _ _
  have heo_s : eo ≤ s / μ := by
    rw [heo]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have heo_e : eo ≤ e₂ / μ := by
    rw [heo]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨fun t => α (ψ t), ee, c₂, μ • w₂, eo, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · show α (ψ 0) = α 0
    rw [hψ0]
  · show α (ψ 1) = α s
    rw [hψ1]
  · rintro x ⟨t, ht, rfl⟩
    exact ⟨ψ t, ⟨hψnn t ht.1, le_trans (hψle t ht.1 ht.2) hs1⟩, rfl⟩
  · exact hαsm.comp hψcmd
  · intro t
    show Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) (α ∘ ψ) t)
    exact TwoRays.injective_mfderiv_comp_reparam_at (n := n) (M := M) (γ := α) (θ := ψ)
      (t := t) hαsm (hαimm (ψ t)) (hmd t) (hstrict t) (ne_of_gt (hψder t))
  · intro x hx y hy hxy
    have hx1 : ψ x ∈ Set.Icc (0:ℝ) 1 :=
      ⟨hψnn x hx.1, le_trans (hψle x hx.1 hx.2) hs1⟩
    have hy1 : ψ y ∈ Set.Icc (0:ℝ) 1 :=
      ⟨hψnn y hy.1, le_trans (hψle y hy.1 hy.2) hs1⟩
    exact hmono.injective (hαinj hx1 hy1 hxy)
  · exact hee_pos
  · intro t ht0 hte
    show α (ψ t) = c.symm (c (α 0) + t • v)
    rw [hψid t hte]
    exact hger t ht0 (le_trans hte hee_le_eps)
  · intro t ht0 hte
    exact htgt t ht0 (le_trans hte hee_le_eps)
  · exact heo_pos
  · exact smul_ne_zero (ne_of_gt hμpos) hw₂
  · exact hc₂
  · exact hsrc₂
  · intro t ht1 ht2
    have hta : a ≤ t := by linarith
    have hψval : ψ t = s + μ * (t - 1) := hψaff t hta ht2
    have hψs : ψ t - s = μ * (t - 1) := by rw [hψval]; ring
    have hle_eo : 1 - t ≤ eo := by linarith
    have hme : μ * (1 - t) ≤ e₂ := by
      have h' : μ * eo ≤ e₂ := by
        have h2 := (le_div_iff₀ hμpos).mp heo_e
        linarith
      exact le_trans (mul_le_mul_of_nonneg_left hle_eo hμpos.le) h'
    have hdiff : |ψ t - s| ≤ e₂ := by
      rw [hψs, abs_mul, abs_of_pos hμpos]
      have h : |t - 1| = 1 - t := by rw [abs_of_nonpos (by linarith)]; ring
      rw [h]; exact hme
    have hnn : 0 ≤ ψ t := by
      have h' : μ * eo ≤ s := by
        have h2 := (le_div_iff₀ hμpos).mp heo_s
        linarith
      have h2 : μ * (1 - t) ≤ s := le_trans (mul_le_mul_of_nonneg_left hle_eo hμpos.le) h'
      have h3 : ψ t = s - μ * (1 - t) := by rw [hψval]; ring
      rw [h3]; linarith
    have hsq : c₂ (α s) + (t - 1) • (μ • w₂) = c₂ (α s) + (ψ t - s) • w₂ := by
      rw [hψs, smul_smul, mul_comm (t - 1) μ]
    rw [hsq]
    exact hger₂ (ψ t) hnn hdiff
  · intro t ht1 ht2
    have hta : a ≤ t := by linarith
    have hψval : ψ t = s + μ * (t - 1) := hψaff t hta ht2
    have hψs : ψ t - s = μ * (t - 1) := by rw [hψval]; ring
    have hle_eo : 1 - t ≤ eo := by linarith
    have hme : μ * (1 - t) ≤ e₂ := by
      have h' : μ * eo ≤ e₂ := by
        have h2 := (le_div_iff₀ hμpos).mp heo_e
        linarith
      exact le_trans (mul_le_mul_of_nonneg_left hle_eo hμpos.le) h'
    have hdiff : |ψ t - s| ≤ e₂ := by
      rw [hψs, abs_mul, abs_of_pos hμpos]
      have h : |t - 1| = 1 - t := by rw [abs_of_nonpos (by linarith)]; ring
      rw [h]; exact hme
    have hnn : 0 ≤ ψ t := by
      have h' : μ * eo ≤ s := by
        have h2 := (le_div_iff₀ hμpos).mp heo_s
        linarith
      have h2 : μ * (1 - t) ≤ s := le_trans (mul_le_mul_of_nonneg_left hle_eo hμpos.le) h'
      have h3 : ψ t = s - μ * (1 - t) := by rw [hψval]; ring
      rw [h3]; linarith
    have hsq : c₂ (α s) + (t - 1) • (μ • w₂) = c₂ (α s) + (ψ t - s) • w₂ := by
      rw [hψs, smul_smul, mul_comm (t - 1) μ]
    have hthis := htgt₂ (ψ t) hnn hdiff
    rwa [← hsq] at hthis

end Work.Drive

import Submission.Work.Smooth.JordanSeparation.Transfer
import Submission.Work.Smooth.JordanSeparation.innerCurve_isSimple
import Submission.Work.Smooth.JordanSeparation.planeSchoenflies_of_injective_extension

/-!
# The collar transfer step (`SCHOENFLIES.md` §2(a)‴)

**(E) can be moved outward along a collar.**  If `c` is a `C¹` immersed simple closed curve carrying
a Lipschitz unit field `v` transverse to it, and the collar of `c` splits as

* the offset points `offset c v (t, u)` with `0 < u < δ` lie in the **bounded** side `S.V`, and
* those with `-δ < u < 0` lie in the **unbounded** side `S.U`

(`hV`, `hU` — the two-dimensional "orientation" input, provided by `collar_side`), then an
injective disc filling of the offset curve `γ' = {offset c v (θ, δ')}` (`0 < δ' < δ`) transfers to
one of `c` itself: `discExtension_of_collar`.

The construction is the one recorded in `SCHOENFLIES.md`:
`F (r e^{iθ}) = offset c v (θ, δ' r)` on the outer half-disc and the filling of `γ'` on the inner
half-disc — the general cylinder transfer `discExtension_of_cylinder` of `Transfer.lean`, applied to
the "shell" cylinder `(t, s) ↦ offset c v (t, δ' s)`.

The verification that the shell stays *outside* `V (γ')` (the hypothesis `havoid` of the cylinder
transfer) is the mathematical content: if the shell lay inside `V (γ')` then the trace of `c`
would too, whence the unbounded side `S.U` (which meets the negative half of the collar, `hU`) would
lie inside `V (γ')` — impossible, since `S.U` is unbounded while `V (γ')` is bounded.

## Main declarations

* `offsetCurve c v s hv hper` — the graph curve `θ ↦ offset c v (θ, s)`;
* `discExtension_of_collar` — the transfer step.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section


/-- The **graph curve** `θ ↦ offset c v (θ, s)` of a plane curve along a periodic field. -/
def offsetCurve (c : SmoothPlaneCurve) (v : ℝ → ℂ) (s : ℝ) (hv : Continuous v)
    (hper : Function.Periodic v (2 * Real.pi)) : PlaneCurve where
  γ := fun θ => offset c v (θ, s)
  cont := (continuous_offset c hv).comp (continuous_id.prodMk continuous_const)
  periodic := fun θ => offset_periodic c hper θ s

@[simp] theorem offsetCurve_apply (c : SmoothPlaneCurve) (v : ℝ → ℂ) (s : ℝ)
    (hv : Continuous v) (hper : Function.Periodic v (2 * Real.pi)) (θ : ℝ) :
    (offsetCurve c v s hv hper) θ = offset c v (θ, s) := rfl

/-- **The collar transfer step.** -/
theorem discExtension_of_collar (c : SmoothPlaneCurve) (himm : SmoothPlaneCurve.IsImmersion c)
    (hs : c.toPlaneCurve.IsSimple)
    {v : ℝ → ℂ} {κ L δ' δ : ℝ} (hκ : 0 < κ) (hL : 0 < L)
    (hδ'pos : 0 < δ') (hδ'δ : δ' < δ) (hδpos : 0 < δ)
    (hvcont : Continuous v) (hvcd : ContDiff ℝ 1 v) (hper : Function.Periodic v (2 * Real.pi))
    (htrans : IsTransverseUnitField c κ v) (hlip : IsLipschitzField L v)
    (hinj : ∀ t t' u u' : ℝ, |u| < δ → |u'| < δ →
      offset c v (t, u) = offset c v (t', u') → u = u' ∧ ∃ k : ℤ, t' = t + k * (2 * Real.pi))
    (hs₁ : (offsetCurve c v δ' hvcont hper).IsSimple)
    (S : PlaneSeparation c.toPlaneCurve)
    (hV : ∀ t u : ℝ, 0 < u → u < δ → offset c v (t, u) ∈ S.V)
    (hU : ∀ t u : ℝ, u < 0 → -δ < u → offset c v (t, u) ∈ S.U) :
    DiscExtension (offsetCurve c v δ' hvcont hper) → DiscExtension c.toPlaneCurve := by
  intro hExt
  set γ₁ : PlaneCurve := offsetCurve c v δ' hvcont hper with hγ₁def
  have hγ₁cd : ContDiff ℝ 1 γ₁.γ := by
    have h1 : γ₁.γ = fun θ : ℝ => c.γ θ + (δ' : ℂ) * v θ := by
      rw [hγ₁def]; funext θ; exact offsetCurve_apply c v δ' hvcont hper θ
    rw [h1]
    exact c.contDiff.add (contDiff_const.mul hvcd)
  obtain ⟨S₁⟩ := jordanSeparation_of_isSimple ⟨γ₁, hγ₁cd⟩ hs₁
  obtain ⟨F₁, hF₁inj, hF₁bd⟩ := hExt
  have hrange : Set.range F₁ = closure S₁.V :=
    range_eq_closure_V_of_injective_extension ⟨γ₁, hγ₁cd⟩ hs₁ S₁ F₁ hF₁inj hF₁bd
  have hδ'abs : |δ'| < δ := by rw [abs_of_pos hδ'pos]; exact hδ'δ
  have hclU : closure S₁.U = S₁.U ∪ γ₁.trace := closure_U_eq_of_isSimple ⟨γ₁, hγ₁cd⟩ hs₁
  have hclV : closure S₁.V = S₁.V ∪ γ₁.trace := closure_V_eq_of_isSimple ⟨γ₁, hγ₁cd⟩ hs₁
  -- a point of the collar is not on the trace of `γ₁`
  have off_notMem : ∀ t u : ℝ, |u| < δ → u ≠ δ' → offset c v (t, u) ∉ γ₁.trace := by
    intro t u hu hu'
    rintro ⟨t', ht'⟩
    have h := hinj t t' u δ' hu hδ'abs (by
      rw [← offsetCurve_apply c v δ' hvcont hper t']; exact ht'.symm)
    exact hu' h.1
  -- the shell
  set Sh : Set ℂ := offset c v '' (Set.univ ×ˢ Set.Ioo (0:ℝ) δ') with hShdef
  have hSh_pre : IsPreconnected Sh := by
    rw [hShdef]
    exact IsPreconnected.image (isPreconnected_univ.prod isPreconnected_Ioo) _
      (continuous_offset c hvcont).continuousOn
  have hSh_off : Sh ⊆ γ₁.traceᶜ := by
    rw [hShdef]
    rintro z ⟨p, ⟨-, hp⟩, rfl⟩
    exact off_notMem p.1 p.2 (by rw [abs_of_pos hp.1]; linarith [hp.2]) (ne_of_lt hp.2)
  have hSh_or : Sh ⊆ S₁.U ∨ Sh ⊆ S₁.V :=
    hSh_pre.subset_or_subset S₁.isOpen_U S₁.isOpen_V S₁.disjoint_UV
      (fun z hz => by rw [S₁.union_eq]; exact hSh_off hz)
  -- the points of the positive half-strip approach the trace of `c`
  have tendsto_pos : ∀ t : ℝ, Filter.Tendsto (fun u : ℝ => offset c v (t, u))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (c.γ t)) := by
    intro t
    have hcont' : Continuous fun u : ℝ => offset c v (t, u) :=
      (continuous_offset c hvcont).comp (continuous_const.prodMk continuous_id)
    have h2 : Filter.Tendsto (fun u : ℝ => offset c v (t, u)) (nhds (0:ℝ))
        (nhds (offset c v (t, 0))) := hcont'.continuousAt (x := 0)
    rw [offset_zero] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  have ev_lt : ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Ioi 0), u < δ' :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hδ'pos)
  -- refutation of `Sh ⊆ S₁.V`
  have hnotV : ¬ Sh ⊆ S₁.V := by
    intro hSV
    have h0mem : c.γ 0 ∈ S₁.V := by
      have hev : ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Ioi 0), offset c v (0, u) ∈ S₁.V := by
        filter_upwards [self_mem_nhdsWithin, ev_lt] with u hu1 hu2
        exact hSV ⟨(0, u), ⟨trivial, ⟨hu1, hu2⟩⟩, rfl⟩
      have hmem := mem_closure_of_tendsto (tendsto_pos 0) hev
      rw [hclV] at hmem
      rcases hmem with h | h
      · exact h
      · exfalso
        obtain ⟨t', ht'⟩ := h
        have h2 := hinj 0 t' 0 δ' (by simpa using hδpos) hδ'abs (by
          rw [offset_zero, ← offsetCurve_apply c v δ' hvcont hper t']; exact ht'.symm)
        exact absurd h2.1 (by linarith)
    -- the ray segment from `c.γ 0` to `offset c v (0, -u)`
    have hrayV : ∀ u : ℝ, 0 < u → u < δ → offset c v (0, -u) ∈ S₁.V := by
      intro u hu huδ
      have hseg_pre : IsPreconnected (offset c v '' ({(0:ℝ)} ×ˢ Set.Icc (-u) 0)) :=
        IsPreconnected.image (isPreconnected_singleton.prod isPreconnected_Icc) _
          (continuous_offset c hvcont).continuousOn
      have hseg_off : offset c v '' ({(0:ℝ)} ×ˢ Set.Icc (-u) 0) ⊆ γ₁.traceᶜ := by
        rintro z ⟨p, ⟨hp1, hp2⟩, rfl⟩
        have hp1' : p.1 = 0 := Set.mem_singleton_iff.mp hp1
        rw [show p = ((0:ℝ), p.2) from Prod.ext hp1' rfl]
        exact off_notMem 0 p.2 (by
          rw [abs_lt]; exact ⟨by linarith [hp2.1], by linarith [hp2.2, huδ]⟩) (by linarith [hp2.2])
      have h0in : c.γ 0 ∈ offset c v '' ({(0:ℝ)} ×ˢ Set.Icc (-u) 0) :=
        ⟨(0, 0), ⟨rfl, ⟨by linarith, le_refl 0⟩⟩, by rw [offset_zero]⟩
      rcases hseg_pre.subset_or_subset S₁.isOpen_U S₁.isOpen_V S₁.disjoint_UV
        (fun z hz => by rw [S₁.union_eq]; exact hseg_off hz) with h | h
      · exfalso
        exact (Set.disjoint_left.mp S₁.disjoint_UV (h h0in)) h0mem
      · exact h ⟨(0, -u), ⟨rfl, ⟨le_refl (-u), by linarith⟩⟩, rfl⟩
    -- `S.U ⊆ S₁.U`
    have hUc : S.U ⊆ S₁.U := by
      have hγ₁V : γ₁.trace ⊆ S.V := by
        rintro z ⟨θ, rfl⟩
        exact hV θ δ' hδ'pos hδ'δ
      have hoff : S.U ⊆ γ₁.traceᶜ := fun z hz hz' => (Set.disjoint_left.mp S.disjoint_UV hz) (hγ₁V hz')
      rcases S.preconn_U.subset_or_subset S₁.isOpen_U S₁.isOpen_V S₁.disjoint_UV
        (fun z hz => by rw [S₁.union_eq]; exact hoff hz) with h | h
      · exact h
      · exfalso
        obtain ⟨R, hR⟩ := ind_vanishes_at_infinity c
        obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0:ℂ)).mp S₁.bounded_V
        obtain ⟨x, hx, hxR⟩ := exists_norm_gt_of_notMem_trace c.toPlaneCurve (max R r)
        have hxU : x ∈ S.U := by
          rw [mem_U_iff_ind_eq_zero_of_isSimple c hs hx]
          exact hR x (by linarith [le_max_left R r, hxR])
        have hxV : x ∈ Metric.closedBall (0:ℂ) r := hr (h hxU)
        rw [Metric.mem_closedBall, dist_zero_right] at hxV
        linarith [le_max_right R r, hxR]
    -- contradiction
    obtain ⟨u₀, hu₀, hu₀δ⟩ : ∃ u : ℝ, 0 < u ∧ u < δ :=
      ⟨δ / 2, by linarith [hδpos], by linarith [hδpos]⟩
    refine (Set.disjoint_left.mp S₁.disjoint_UV (hUc (hU 0 (-u₀) (by linarith) (by linarith))))
      (hrayV u₀ hu₀ hu₀δ)
  have hShU : Sh ⊆ S₁.U := hSh_or.resolve_right hnotV
  -- hence the trace of `c` lies in `S₁.U`
  have hcU : c.toPlaneCurve.trace ⊆ S₁.U := by
    have hsub : c.toPlaneCurve.trace ⊆ closure S₁.U := by
      rintro z hz
      obtain ⟨θ, hθ⟩ := hz
      rw [← hθ]
      refine mem_closure_of_tendsto (tendsto_pos θ) ?_
      filter_upwards [self_mem_nhdsWithin, ev_lt] with u hu1 hu2
      exact hShU ⟨(θ, u), ⟨trivial, ⟨hu1, hu2⟩⟩, rfl⟩
    rw [hclU] at hsub
    intro z hz
    rcases hsub hz with h | h
    · exact h
    · exfalso
      obtain ⟨t', ht'⟩ := h
      obtain ⟨θ, hθ⟩ := hz
      have h2 := hinj θ t' 0 δ' (by simpa using hδpos) hδ'abs (by
        rw [offset_zero, ← offsetCurve_apply c v δ' hvcont hper t']; exact hθ.trans ht'.symm)
      exact absurd h2.1 (by linarith)
  -- the transfer
  have hΦcont : Continuous fun p : ℝ × ℝ => offset c v (p.1, δ' * p.2) :=
    (continuous_offset c hvcont).comp (continuous_fst.prodMk (continuous_snd.const_mul δ'))
  have hΦper : ∀ t s : ℝ, offset c v (t + 2 * Real.pi, δ' * s) = offset c v (t, δ' * s) :=
    fun t s => offset_periodic c hper t (δ' * s)
  have hΦzero : ∀ t : ℝ, offset c v (t, δ' * 0) = c.toPlaneCurve.γ t := by
    intro t; rw [mul_zero, offset_zero]
  have hΦone : ∀ t : ℝ, offset c v (t, δ' * 1) = γ₁.γ t := by
    intro t; rw [mul_one]; exact (offsetCurve_apply c v δ' hvcont hper t).symm
  have habsδ : ∀ s : ℝ, s ∈ Set.Icc (0:ℝ) 1 → |δ' * s| < δ := by
    intro s hsst
    rw [abs_of_nonneg (mul_nonneg hδ'pos.le hsst.1)]
    calc δ' * s ≤ δ' * 1 := mul_le_mul_of_nonneg_left hsst.2 hδ'pos.le
      _ = δ' := mul_one δ'
      _ < δ := hδ'δ
  have hΦinj : ∀ t s t' s' : ℝ, s ∈ Set.Icc (0:ℝ) 1 → s' ∈ Set.Icc (0:ℝ) 1 →
      offset c v (t, δ' * s) = offset c v (t', δ' * s') →
      s = s' ∧ ∃ k : ℤ, t' = t + k * (2 * Real.pi) := by
    intro t s t' s' hsst hsst' heq
    obtain ⟨huv, k, hk⟩ := hinj t t' (δ' * s) (δ' * s') (habsδ s hsst) (habsδ s' hsst') heq
    exact ⟨mul_left_cancel₀ (ne_of_gt hδ'pos) huv, k, hk⟩
  have hΦavoid : ∀ t s : ℝ, s ∈ Set.Icc (0:ℝ) 1 → s < 1 →
      offset c v (t, δ' * s) ∉ Set.range F₁ := by
    intro t s hsst hslt
    rw [hrange, hclV]
    rcases eq_or_lt_of_le hsst.1 with h0 | h0
    · rw [← h0, mul_zero, offset_zero]
      rintro (hmem | hmem)
      · exact (Set.disjoint_left.mp S₁.disjoint_UV
          (hcU (PlaneCurve.mem_trace c.toPlaneCurve t))) hmem
      · obtain ⟨t', ht'⟩ := hmem
        have h2 := hinj t t' 0 δ' (by simpa using hδpos) hδ'abs (by
          rw [offset_zero, ← offsetCurve_apply c v δ' hvcont hper t']; exact ht'.symm)
        exact absurd h2.1 (by linarith)
    · intro hmem
      rcases hmem with h | h
      · have hmemSh : offset c v (t, δ' * s) ∈ Sh :=
          ⟨(t, δ' * s), ⟨trivial, ⟨by positivity, by nlinarith [h0, hslt, hδ'pos]⟩⟩, rfl⟩
        exact (Set.disjoint_left.mp S₁.disjoint_UV (hShU hmemSh)) h
      · exfalso
        obtain ⟨t', ht'⟩ := h
        have h2 := hinj t t' (δ' * s) δ' (habsδ s hsst) hδ'abs (by
          rw [← offsetCurve_apply c v δ' hvcont hper t']; exact ht'.symm)
        nlinarith [h2.1, h0, hslt, hδ'pos]
  exact discExtension_of_cylinder c.toPlaneCurve γ₁ (fun p : ℝ × ℝ => offset c v (p.1, δ' * p.2))
    hΦcont hΦper hΦzero hΦone hΦinj F₁ hF₁inj hF₁bd hΦavoid

end

end Work.Smooth.JordanSeparation

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- `DiscExtension` only depends on the curve function. -/
theorem discExtension_congr {γ γ' : PlaneCurve} (h : γ.γ = γ'.γ) :
    DiscExtension γ ↔ DiscExtension γ' := by
  constructor <;> rintro ⟨F, hinj, hbd⟩
  · exact ⟨F, hinj, fun θ => by rw [← h]; exact hbd θ⟩
  · exact ⟨F, hinj, fun θ => by rw [h]; exact hbd θ⟩

/-- The offset curve of `-v` is the offset curve of `v` at the opposite depth. -/
theorem offsetCurve_neg (c : SmoothPlaneCurve) (v : ℝ → ℂ) (s : ℝ) (hv : Continuous v)
    (hper : Function.Periodic v (2 * Real.pi)) :
    (offsetCurve c (fun t => -v t) s hv.neg
        (fun t => by simp [hper t])).γ = (offsetCurve c v (-s) hv hper).γ := by
  funext θ
  show c.γ θ + (s : ℂ) * (-(v θ)) = c.γ θ + ((-s : ℝ) : ℂ) * v θ
  push_cast
  ring

/-- **The collar transfer step, in the orientation in which the *negative* half of the collar lies
in the bounded side.**  A filling of the offset curve at depth `-δ'` (the inner offset in that
orientation) transfers to `c`. -/
theorem discExtension_of_collar_neg (c : SmoothPlaneCurve) (himm : SmoothPlaneCurve.IsImmersion c)
    (hs : c.toPlaneCurve.IsSimple)
    {v : ℝ → ℂ} {κ L δ' δ : ℝ} (hκ : 0 < κ) (hL : 0 < L)
    (hδ'pos : 0 < δ') (hδ'δ : δ' < δ) (hδpos : 0 < δ)
    (hvcont : Continuous v) (hvcd : ContDiff ℝ 1 v) (hper : Function.Periodic v (2 * Real.pi))
    (htrans : IsTransverseUnitField c κ v) (hlip : IsLipschitzField L v)
    (hinj : ∀ t t' u u' : ℝ, |u| < δ → |u'| < δ →
      offset c v (t, u) = offset c v (t', u') → u = u' ∧ ∃ k : ℤ, t' = t + k * (2 * Real.pi))
    (hs₁ : (offsetCurve c v δ' hvcont hper).IsSimple)
    (hs₁' : (offsetCurve c v (-δ') hvcont hper).IsSimple)
    (S : PlaneSeparation c.toPlaneCurve)
    (hV : ∀ t u : ℝ, u < 0 → -δ < u → offset c v (t, u) ∈ S.V)
    (hU : ∀ t u : ℝ, 0 < u → u < δ → offset c v (t, u) ∈ S.U)
    (hExt : DiscExtension (offsetCurve c v (-δ') hvcont hper)) :
    DiscExtension c.toPlaneCurve := by
  have hper' : Function.Periodic (fun t => -v t) (2 * Real.pi) := fun t => by simp [hper t]
  have hcont' : Continuous (fun t => -v t) := hvcont.neg
  have htrans' : IsTransverseUnitField c κ (fun t => -v t) :=
    ⟨fun t => by simpa using htrans.1 t, fun t => by
      have h := htrans.2 t
      rw [show (fun t => -v t) t = -(v t) from rfl, detV_neg_right, abs_neg]
      exact h⟩
  have hlip' : IsLipschitzField L (fun t => -v t) := fun t t' => by
    have h := hlip t t'
    have heq : (fun t => -v t) t - (fun t => -v t) t' = -(v t - v t') := by ring
    rw [heq, norm_neg]
    exact h
  have hinj' : ∀ t t' u u' : ℝ, |u| < δ → |u'| < δ →
      offset c (fun t => -v t) (t, u) = offset c (fun t => -v t) (t', u') →
      u = u' ∧ ∃ k : ℤ, t' = t + k * (2 * Real.pi) := by
    intro t t' u u' hu hu' heq
    have heq' : offset c v (t, -u) = offset c v (t', -u') := by
      simpa [offset] using heq
    obtain ⟨huv, k, hk⟩ := hinj t t' (-u) (-u') (by simpa using hu) (by simpa using hu') heq'
    exact ⟨by linarith, k, hk⟩
  have hV' : ∀ t u : ℝ, 0 < u → u < δ → offset c (fun t => -v t) (t, u) ∈ S.V := by
    intro t u hu huδ
    have : offset c (fun t => -v t) (t, u) = offset c v (t, -u) := by
      simp only [offset]; push_cast; ring
    rw [this]
    exact hV t (-u) (by linarith) (by linarith)
  have hU' : ∀ t u : ℝ, u < 0 → -δ < u → offset c (fun t => -v t) (t, u) ∈ S.U := by
    intro t u hu huδ
    have : offset c (fun t => -v t) (t, u) = offset c v (t, -u) := by
      simp only [offset]; push_cast; ring
    rw [this]
    exact hU t (-u) (by linarith) (by linarith)
  have hExt' : DiscExtension (offsetCurve c (fun t => -v t) δ' hcont' hper') := by
    rw [discExtension_congr (offsetCurve_neg c v δ' hvcont hper)]
    exact hExt
  refine discExtension_of_collar c himm hs hκ hL hδ'pos hδ'δ hδpos hcont' hvcd.neg hper' htrans'
    hlip' hinj' ?_ S hV' hU' hExt'
  show Set.InjOn (offsetCurve c (fun t => -v t) δ' hcont' hper').γ (Set.Ico 0 (2 * Real.pi))
  rw [offsetCurve_neg c v δ' hvcont hper]
  exact hs₁'

end

end Work.Smooth.JordanSeparation

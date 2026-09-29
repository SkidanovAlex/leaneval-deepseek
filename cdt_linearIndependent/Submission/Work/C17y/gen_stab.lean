import Mathlib
import Submission.Work.C17y.gen_van
import Submission.Work.C17y.hasDerivAt_wev
import Submission.Work.C17y.hasDerivAt_wev_bzero

/-!
# `∂` preserves the vanishing predicate

`Van x0 δ y1 J n` says that the relation function `Wev y1 J n` vanishes on the ball `ball x0 δ` off
a finite set.  Here we prove that it is preserved by the connection `Dv` (differentiation of the
relation, with the second derivative of `y1` eliminated by the ODE), so that the relation module
`Nsub` is `Dv`-stable.

If the `y1'`-coefficient `b = n.2.1` vanishes, the relation involves no second derivative and
`Work.C17y.hasDerivAt_wev_bzero` applies.  If `b ≠ 0`, the relation *expresses* `y1'` rationally in
terms of `y1` and the `J i`, so `deriv y1` is differentiable at each point where the relation holds
and `b` does not vanish; there `Work.C17y.hasDerivAt_wev` applies.
-/

namespace Work.C17y

open Complex Metric
open scoped Topology
open Submission.CDT (dRat)
open Work.GenShared (Rval Rreg W Dv Wev hasDerivAt_rval)

noncomputable section

lemma mem_zeroFinset (p : Polynomial ℂ) (hp : p ≠ 0) (z : ℂ) :
    z ∈ (Polynomial.finite_setOfPred_isRoot hp).toFinset ↔ p.eval z = 0 := by
  rw [Set.Finite.mem_toFinset]
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def]

lemma mem_rdFinset {k : ℕ} (rd : Fin k → Polynomial ℂ) (hrdne : ∀ i, rd i ≠ 0) (z : ℂ) :
    z ∈ (Finset.univ.biUnion fun i : Fin k =>
        (Polynomial.finite_setOfPred_isRoot (hrdne i)).toFinset) ↔ ∃ i, (rd i).eval z = 0 := by
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨i, -, hi⟩; exact ⟨i, (mem_zeroFinset (rd i) (hrdne i) z).mp hi⟩
  · rintro ⟨i, hi⟩; exact ⟨i, Finset.mem_univ i, (mem_zeroFinset (rd i) (hrdne i) z).mpr hi⟩

lemma notMem_coe {s : Finset ℂ} {z : ℂ} (h : z ∉ (s : Set ℂ)) : z ∉ s :=
  fun hh => h (Finset.mem_coe.mpr hh)

/-- The finite exceptional set for the `Dv`-stability proof: the original exceptional set, the poles
of the two coefficient tuples, the zeros of `p2` and of the `rd i`. -/
def badFinset {k : ℕ} (p2 : Polynomial ℂ) (hp2 : p2 ≠ 0) (rd : Fin k → Polynomial ℂ)
    (hrdne : ∀ i, rd i ≠ 0) (n n' : W k) (F : Finset ℂ) : Finset ℂ :=
  (((F ∪ (polesSet_finite n).toFinset) ∪ (polesSet_finite n').toFinset)
    ∪ (Polynomial.finite_setOfPred_isRoot hp2).toFinset)
    ∪ (Finset.univ.biUnion fun i : Fin k =>
        (Polynomial.finite_setOfPred_isRoot (hrdne i)).toFinset)

lemma notMem_badFinset {k : ℕ} {p2 : Polynomial ℂ} (hp2 : p2 ≠ 0) {rd : Fin k → Polynomial ℂ}
    (hrdne : ∀ i, rd i ≠ 0) {n n' : W k} {F : Finset ℂ} {z : ℂ} :
    z ∉ badFinset p2 hp2 rd hrdne n n' F ↔
      (z ∉ F ∧ z ∉ (polesSet_finite n).toFinset ∧ z ∉ (polesSet_finite n').toFinset
        ∧ z ∉ (Polynomial.finite_setOfPred_isRoot hp2).toFinset
        ∧ z ∉ (Finset.univ.biUnion fun i : Fin k =>
            (Polynomial.finite_setOfPred_isRoot (hrdne i)).toFinset)) := by
  rw [badFinset]
  simp only [Finset.mem_union, not_or, and_assoc]

/-- The poles set, the zeros of `p2` and the zeros of the `rd i` never contain all points of the
ball, so the following reformulation of the extraction is available. -/
lemma extract {k : ℕ} {p2 : Polynomial ℂ} (hp2 : p2 ≠ 0) {rd : Fin k → Polynomial ℂ}
    (hrdne : ∀ i, rd i ≠ 0) {n n' : W k} {F : Finset ℂ} {z : ℂ}
    (h : z ∉ (badFinset p2 hp2 rd hrdne n n' F : Set ℂ)) :
    (z ∉ (F : Set ℂ)) ∧ (z ∉ polesSet n) ∧ (z ∉ polesSet n')
      ∧ p2.eval z ≠ 0 ∧ (∀ i, (rd i).eval z ≠ 0) := by
  have h' := (notMem_badFinset hp2 hrdne).mp (notMem_coe h)
  obtain ⟨hF, hP, hP', hp2z, hrdz⟩ := h'
  refine ⟨fun hh => hF (Finset.mem_coe.mpr hh), ?_, ?_, ?_, ?_⟩
  · exact fun hh => hP ((Set.Finite.mem_toFinset (polesSet_finite n)).mpr hh)
  · exact fun hh => hP' ((Set.Finite.mem_toFinset (polesSet_finite n')).mpr hh)
  · exact fun hh => hp2z ((mem_zeroFinset p2 hp2) z |>.mpr hh)
  · intro i hh
    refine hrdz (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩)
    exact (mem_zeroFinset (rd i) (hrdne i) z).mpr hh

/-- **`∂` preserves `Van`.** -/
theorem van_dv {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (rn rd : Fin k → Polynomial ℂ)
    (hp2ne : p2 ≠ 0) (hrdne : ∀ i, rd i ≠ 0)
    {x0 : ℂ} {δ : ℝ} {y1 : ℂ → ℂ} {J : Fin k → ℂ → ℂ}
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball x0 δ))
    (hJd : ∀ i, DifferentiableOn ℂ (J i) (Metric.ball x0 δ))
    (hode : ∀ w ∈ Metric.ball x0 δ,
      p2.eval w * deriv (deriv y1) w + p1.eval w * deriv y1 w + p0.eval w * y1 w = 0)
    (hJderiv : ∀ i, ∀ w ∈ Metric.ball x0 δ,
      HasDerivAt (J i) ((rn i).eval w / (rd i).eval w * y1 w) w)
    {n : W k} (hn : Van x0 δ y1 J n) :
    Van x0 δ y1 J (Dv p2 p1 p0 rn rd n) := by
  obtain ⟨a, b, c⟩ := n
  obtain ⟨F, hF⟩ := hn
  -- the open neighbourhood on which the relation holds and the coefficients are regular
  have hopen : IsOpen (Metric.ball x0 δ \ ((F ∪ (polesSet_finite (a, b, c)).toFinset : Finset ℂ)
      : Set ℂ)) := Metric.isOpen_ball.sdiff (Finset.finite_toSet _).isClosed
  have hrel_near : ∀ {z : ℂ}, z ∈ Metric.ball x0 δ → z ∉ (F : Set ℂ) →
      z ∉ (polesSet_finite (a, b, c)).toFinset →
      (∀ᶠ w in 𝓝 z, Wev y1 J (a, b, c) w = 0 ∧ w ∉ (polesSet (a, b, c)) ∧ w ∈ Metric.ball x0 δ) := by
    intro z hz hzF hzP
    have hzE : z ∈ Metric.ball x0 δ \ ((F ∪ (polesSet_finite (a, b, c)).toFinset : Finset ℂ)
        : Set ℂ) := by
      refine ⟨hz, ?_⟩
      simp only [Finset.mem_coe, Finset.mem_union]
      exact not_or.mpr ⟨fun h => hzF h, fun h => hzP h⟩
    have hPopen : IsOpen ((polesSet (a, b, c))ᶜ) := (polesSet_finite _).isClosed.isOpen_compl
    have hzPopen : z ∈ (polesSet (a, b, c))ᶜ := fun h => hzP ((Set.Finite.mem_toFinset _).mpr h)
    filter_upwards [hopen.mem_nhds hzE, hPopen.mem_nhds hzPopen] with w hw hw'
    exact ⟨hF w hw.1 (fun h => hw.2 (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl h)))),
      hw', hw.1⟩
  by_cases hb : b = 0
  · -- ## Case `b = 0`: no second derivative occurs
    subst hb
    refine ⟨badFinset p2 hp2ne rd hrdne (a, (0 : RatFunc ℂ), c)
      (Dv p2 p1 p0 rn rd (a, (0 : RatFunc ℂ), c)) F, fun z hz hzS => ?_⟩
    obtain ⟨hzF, hzP, -, hp2, hrd⟩ := extract hp2ne hrdne hzS
    obtain ⟨ha, -, hc⟩ := not_mem_polesSet hzP
    have hzP1 : z ∉ (polesSet_finite (a, (0 : RatFunc ℂ), c)).toFinset :=
      fun h => hzP ((Set.Finite.mem_toFinset _).mp h)
    have hev := hrel_near hz hzF hzP1
    have hev' : (fun w => Wev y1 J (a, (0 : RatFunc ℂ), c) w) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) :=
      hev.mono fun w hw => hw.1
    have hderiv : deriv (fun w => Wev y1 J (a, (0 : RatFunc ℂ), c) w) z = 0 := by
      rw [hev'.deriv_eq]; simp
    have hHas := hasDerivAt_wev_bzero p2 p1 p0 rn rd hz hy1d hJderiv hp2 hrd ha hc
    have hfun : (fun w => Wev y1 J (a, (0 : RatFunc ℂ), c) w)
        = fun w => Rval a w * y1 w + ∑ i, Rval (c i) w * J i w := by
      funext w; simp [Wev, Rval]
    rw [hfun] at hderiv
    rw [← hHas.deriv, hderiv]
  · -- ## Case `b ≠ 0`: the relation expresses `y1'`
    set Zb : Finset ℂ := (Polynomial.finite_setOfPred_isRoot (RatFunc.num_ne_zero hb)).toFinset
      with hZb
    refine ⟨badFinset p2 hp2ne rd hrdne (a, b, c) (Dv p2 p1 p0 rn rd (a, b, c)) F ∪ Zb,
      fun z hz hzS => ?_⟩
    have hzU : z ∉ (badFinset p2 hp2ne rd hrdne (a, b, c) (Dv p2 p1 p0 rn rd (a, b, c)) F
        : Set ℂ) :=
      fun h => hzS (Finset.mem_union.mpr (Or.inl (Finset.mem_coe.mpr h)))
    obtain ⟨hzF, hzP, hzP', hp2, hrd⟩ := extract hp2ne hrdne hzU
    have hzZb : z ∉ Zb := fun h => hzS (Finset.mem_union.mpr (Or.inr h))
    obtain ⟨ha, hbreg, hc⟩ := not_mem_polesSet hzP
    have hzZb' : z ∉ (Polynomial.finite_setOfPred_isRoot (RatFunc.num_ne_zero hb)).toFinset := by
      rwa [hZb] at hzZb
    have hbnum : b.num.eval z ≠ 0 := fun h =>
      hzZb' ((mem_zeroFinset b.num (RatFunc.num_ne_zero hb) z).mpr h)
    have hbval : Rval b z ≠ 0 := by rw [Rval]; exact div_ne_zero hbnum hbreg
    have hzP1 : z ∉ (polesSet_finite (a, b, c)).toFinset :=
      fun h => hzP ((Set.Finite.mem_toFinset _).mp h)
    -- the relation expresses `deriv y1` near `z`
    have hEopen : IsOpen ((Metric.ball x0 δ \ ((F ∪ (polesSet_finite (a, b, c)).toFinset
          : Finset ℂ) : Set ℂ)) ∩ {w : ℂ | b.num.eval w ≠ 0} ∩ {w : ℂ | b.denom.eval w ≠ 0}) := by
      refine IsOpen.inter (IsOpen.inter hopen ?_) ?_
      · exact (Polynomial.finite_setOfPred_isRoot (RatFunc.num_ne_zero hb)).isClosed.isOpen_compl
      · exact (Polynomial.finite_setOfPred_isRoot (RatFunc.denom_ne_zero b)).isClosed.isOpen_compl
    have hzE2 : z ∈ (Metric.ball x0 δ \ ((F ∪ (polesSet_finite (a, b, c)).toFinset : Finset ℂ)
        : Set ℂ)) ∩ {w : ℂ | b.num.eval w ≠ 0} ∩ {w : ℂ | b.denom.eval w ≠ 0} := by
      refine ⟨⟨⟨hz, ?_⟩, hbnum⟩, hbreg⟩
      simp only [Finset.mem_coe, Finset.mem_union]
      exact not_or.mpr ⟨fun h => hzF h, fun h => hzP1 h⟩
    have hAgree : (fun w => deriv y1 w) =ᶠ[𝓝 z]
        (fun w => -((Rval a w * y1 w + ∑ i, Rval (c i) w * J i w) / Rval b w)) := by
      filter_upwards [hEopen.mem_nhds hzE2] with w hw
      obtain ⟨⟨⟨hwball, hwF⟩, hwnum⟩, hwden⟩ := hw
      have hwF' : w ∉ (F : Set ℂ) :=
        fun h => hwF (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl h)))
      have hwP : w ∉ polesSet (a, b, c) := fun h =>
        hwF (Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr
          ((Set.Finite.mem_toFinset (polesSet_finite (a, b, c))).mpr h))))
      obtain ⟨hwa, -, hwc⟩ := not_mem_polesSet hwP
      have hrel := hF w hwball hwF'
      have hrel' : Rval a w * y1 w + Rval b w * deriv y1 w
          + ∑ i, Rval (c i) w * J i w = 0 := by
        simpa only [Wev] using hrel
      have hbw : Rval b w ≠ 0 := by rw [Rval]; exact div_ne_zero hwnum hwden
      have hBX : Rval b w * deriv y1 w
          + (Rval a w * y1 w + ∑ i, Rval (c i) w * J i w) = 0 := by
        rw [← hrel']; ring
      rw [← neg_div, eq_div_iff hbw, mul_comm]
      exact eq_neg_iff_add_eq_zero.mpr hBX
    have hdiffψ : DifferentiableAt ℂ
        (fun w => -((Rval a w * y1 w + ∑ i, Rval (c i) w * J i w) / Rval b w)) z := by
      refine DifferentiableAt.neg (DifferentiableAt.div ?_ ?_ hbval)
      · refine DifferentiableAt.add ?_ ?_
        · exact (hasDerivAt_rval a z ha).differentiableAt.mul
            (hy1d.differentiableAt (Metric.isOpen_ball.mem_nhds hz))
        · have hterm : ∀ i : Fin k, DifferentiableAt ℂ (fun w => Rval (c i) w * J i w) z :=
            fun i => (hasDerivAt_rval (c i) z (hc i)).differentiableAt.mul
              (hJderiv i z hz).differentiableAt
          have h := DifferentiableAt.sum (u := Finset.univ)
            (fun i (_ : i ∈ Finset.univ) => hterm i)
          have hfun : (∑ i, fun w => Rval (c i) w * J i w)
              = fun w => ∑ i, Rval (c i) w * J i w := by
            funext w; simp [Finset.sum_apply]
          rwa [hfun] at h
      · exact (hasDerivAt_rval b z hbreg).differentiableAt
    have hy1'' : DifferentiableAt ℂ (deriv y1) z := hAgree.differentiableAt_iff.mpr hdiffψ
    -- the relation function vanishes near `z`
    have hev := hrel_near hz hzF hzP1
    have hev' : (fun w => Wev y1 J (a, b, c) w) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) :=
      hev.mono fun w hw => hw.1
    have hderiv : deriv (fun w => Wev y1 J (a, b, c) w) z = 0 := by
      rw [hev'.deriv_eq]; simp
    have hHas := hasDerivAt_wev p2 p1 p0 rn rd hz hy1d hJd hode hJderiv hp2 hrd hy1'' ha hbreg hc
    rw [← hHas.deriv, hderiv]

end

end Work.C17y

import Mathlib
import Submission.Work.Horn.flower_q

/-!
# Simply connectedness of the Leau–Fatou petals

`Work.Horn.flower_q` produces `q` disjoint open connected petals `V j = Flower.petal q a M j` for a
parabolic germ `f z = z + a z^(q+1) + o(z^(q+1))`.  This file adds the one property that
`flower_q` does not state: each petal is **simply connected**.

The petal is `rootFun q a j '' DM q a M`, where

* `DM q a M = {s | M * ‖s‖² < Re (c * conj s)}` is the open disc
  `Metric.ball (c / (2M)) (‖c‖ / (2M))` (`c = cc q a = -1/(q a)`), hence contractible; and
* `rootFun q a j s = ζ_j * exp (log (s/c) / q)` is a branch of the `q`-th root.

The map `s ↦ rootFun q a j s` is continuous on `DM` (the point `s/c` always lies in the slit plane
because `Re (c * conj s) > M ‖s‖² > 0`), it is injective on `DM` (`rootFun_pow` recovers `s` as the
`q`-th power), and its inverse on the petal is the continuous map `z ↦ z ^ q`.  Hence it is a
homeomorphism `DM ≃ₜ petal`, and `SimplyConnectedSpace` transfers.
-/

set_option linter.style.haveILetI false

namespace Work.Horn

open Filter Topology
open scoped Topology
open Work.Horn.Flower

/-- On the root disc `DM q a M` the quotient `s / cc q a` lies in the slit plane: indeed
`Re (cc q a * conj s) > M ‖s‖² > 0` forces `s ≠ 0` and
`Re (s / cc q a) = Re (cc q a * conj s) / normSq (cc q a) > 0`. -/
theorem flower_div_cc_mem_slitPlane {q : ℕ} {a : ℂ} {M : ℝ} (hM : 0 < M)
    (hcc : cc q a ≠ 0) {s : ℂ} (hs : s ∈ DM q a M) :
    s / cc q a ∈ Complex.slitPlane := by
  have hs' : M * Complex.normSq s < (cc q a * star s).re := hs
  have hc : 0 < Complex.normSq (cc q a) := Complex.normSq_pos.mpr hcc
  have hsne : s ≠ 0 := by
    intro h; rw [h] at hs'; simp at hs'
  have hns : 0 < Complex.normSq s := Complex.normSq_pos.mpr hsne
  have hre : (s / cc q a).re = (cc q a * star s).re / Complex.normSq (cc q a) := by
    rw [Complex.div_re, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  refine Or.inl ?_
  rw [hre]
  apply div_pos _ hc
  have h2 : 0 < M * Complex.normSq s := mul_pos hM hns
  linarith [hs']

/-- The branch `rootFun q a j` of the `q`-th root is continuous on the root disc. -/
theorem flower_continuous_rootFun_DM {q : ℕ} {a : ℂ} {M : ℝ} (hM : 0 < M) (hcc : cc q a ≠ 0)
    (j : Fin q) : Continuous (fun s : DM q a M => rootFun q a j (s : ℂ)) := by
  have h1 : Continuous (fun s : ↥(DM q a M) => (s : ℂ) / cc q a) :=
    continuous_subtype_val.div_const (cc q a)
  have h2 : ∀ s : ↥(DM q a M), ((s : ℂ) / cc q a) ∈ Complex.slitPlane :=
    fun s => flower_div_cc_mem_slitPlane hM hcc s.2
  have hlog : Continuous (fun s : ↥(DM q a M) => Complex.log ((s : ℂ) / cc q a)) := h1.clog h2
  have hexp : Continuous
      (fun s : ↥(DM q a M) => Complex.exp (Complex.log ((s : ℂ) / cc q a) / (q : ℂ))) :=
    Complex.continuous_exp.comp (hlog.div_const (q : ℂ))
  have h3 : Continuous (fun s : ↥(DM q a M) =>
      zeta q a j * Complex.exp (Complex.log ((s : ℂ) / cc q a) / (q : ℂ))) :=
    continuous_const.mul hexp
  simpa [rootFun] using h3

/-- The `j`-th petal is homeomorphic to the root disc `DM q a M`: the `q`-th root branch
`rootFun q a j` is injective with continuous inverse `z ↦ z ^ q`. -/
theorem flower_petal_homeomorph_DM {q : ℕ} {a : ℂ} {M : ℝ} (hM : 0 < M) (hcc : cc q a ≠ 0)
    (hgeo : PetalFacts q a M) (j : Fin q) :
    Nonempty (↥(DM q a M) ≃ₜ ↥(petal q a M j)) := by
  have hpow : ∀ z : ↥(petal q a M j), (z : ℂ) ^ q ∈ DM q a M := by
    intro z
    obtain ⟨s, hs, hsz⟩ := z.2
    rw [← hsz, hgeo.rootFun_pow j s hs]
    exact hs
  have hback : ∀ z : ↥(petal q a M j), rootFun q a j ((z : ℂ) ^ q) = (z : ℂ) := by
    intro z
    obtain ⟨s, hs, hsz⟩ := z.2
    rw [← hsz, hgeo.rootFun_pow j s hs]
  refine ⟨{ toFun := fun s => ⟨rootFun q a j (s : ℂ), ⟨(s : ℂ), s.2, rfl⟩⟩
           , invFun := fun z => ⟨(z : ℂ) ^ q, hpow z⟩
           , left_inv := ?_
           , right_inv := ?_
           , continuous_toFun := ?_
           , continuous_invFun := ?_ }⟩
  · intro s
    exact Subtype.ext (hgeo.rootFun_pow j (s : ℂ) s.2)
  · intro z
    exact Subtype.ext (hback z)
  · exact Continuous.subtype_mk (flower_continuous_rootFun_DM hM hcc j)
      (fun s => ⟨(s : ℂ), s.2, rfl⟩)
  · exact Continuous.subtype_mk (continuous_subtype_val.pow q) hpow

/-- Each Leau–Fatou petal is simply connected. -/
theorem flower_petal_simplyConnected {q : ℕ} {a : ℂ} {M : ℝ} (hM : 0 < M)
    (hgeo : PetalFacts q a M) (j : Fin q) : SimplyConnectedSpace (petal q a M j) := by
  obtain ⟨e⟩ := flower_petal_homeomorph_DM hM hgeo.cc_ne_zero hgeo j
  have hpos : 0 < ‖cc q a‖ / (2 * M) := div_pos (norm_pos_iff.mpr hgeo.cc_ne_zero) (by positivity)
  have hDM : SimplyConnectedSpace ↥(DM q a M) := by
    rw [hgeo.DM_eq_ball]
    haveI : ContractibleSpace ↥(Metric.ball (cc q a / (2 * M)) (‖cc q a‖ / (2 * M))) :=
      Metric.contractibleSpace_ball hpos
    infer_instance
  haveI := hDM
  exact e.symm.toHomotopyEquiv.simplyConnectedSpace

theorem flower_q_simplyConnected {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ}
    (hD : IsOpen D) (hconn : IsPreconnected D) (h0 : (0 : ℂ) ∈ D) (hf : DifferentiableOn ℂ f D)
    (hq : 1 ≤ q) (ha : a ≠ 0) (hfix : f 0 = 0)
    (hgerm : Filter.Tendsto (fun z : ℂ => (f z - z - a * z ^ (q + 1)) / z ^ (q + 1))
      (nhdsWithin 0 {0}ᶜ) (nhds 0)) :
    ∃ V : Fin q → Set ℂ,
      (∀ (i : Fin q), IsOpen (V i) ∧ IsConnected (V i) ∧ SimplyConnectedSpace (V i) ∧ V i ⊆ D) ∧
      (∀ (i : Fin q), ∀ z ∈ V i, f z ∈ V i ∪ {0}) ∧
      (∀ (i j : Fin q), i ≠ j → Disjoint (V i) (V j)) ∧
      (∀ (i : Fin q), (0 : ℂ) ∈ closure (V i)) ∧
      (∀ (i : Fin q), Set.InjOn f (V i)) := by
  have hS : Flower.Setup f D q a := ⟨hD, hconn, h0, hf, hq, ha, hfix, hgerm⟩
  obtain ⟨ρ, hρ, hb⟩ := bounds_exists hS
  have hcc : Flower.cc q a ≠ 0 := by
    rw [Flower.cc]
    exact div_ne_zero (by norm_num) (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) ha)
  have hccpos : 0 < ‖Flower.cc q a‖ := norm_pos_iff.mpr hcc
  have hρq : 0 < ρ ^ q := pow_pos hρ q
  set M : ℝ := ‖Flower.cc q a‖ / ρ ^ q + 1 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hRM : ‖Flower.cc q a‖ / M < ρ ^ q := by
    have h1 : ‖Flower.cc q a‖ / ρ ^ q < M := by rw [hMdef]; linarith
    have h2 : ‖Flower.cc q a‖ / M < ‖Flower.cc q a‖ / (‖Flower.cc q a‖ / ρ ^ q) :=
      div_lt_div_of_pos_left hccpos (div_pos hccpos hρq) h1
    have h3 : ‖Flower.cc q a‖ / (‖Flower.cc q a‖ / ρ ^ q) = ρ ^ q := by field_simp
    rwa [h3] at h2
  have hgeo : Flower.PetalFacts q a M := petal_facts hq ha hMpos
  have hlogpow : ∀ u : ℂ, u ≠ 0 → |u.arg| * (q : ℝ) < Real.pi →
      Complex.log (u ^ q) = (q : ℂ) * Complex.log u :=
    fun u hu hu' => log_pow_eq hq hu hu'
  have hmaps : ∀ j : Fin q, Set.MapsTo f (Flower.petal q a M j) (Flower.petal q a M j ∪ {0}) :=
    petal_mapsTo hb hMpos hRM hgeo hlogpow
  have hball : ∀ j : Fin q, Flower.petal q a M j ⊆ Metric.ball (0 : ℂ) ρ := by
    intro j z hz
    have h1 : ‖z‖ ^ q < ‖Flower.cc q a‖ / M := hgeo.petal_norm_pow_lt j z hz
    have h2 : ‖z‖ ^ q < ρ ^ q := lt_trans h1 hRM
    have h3 : ‖z‖ < ρ := by
      by_contra hcon
      push Not at hcon
      exact absurd h2 (not_lt.mpr (pow_le_pow_left₀ hρ.le hcon q))
    simpa [Metric.mem_ball, dist_zero_right] using h3
  have hinj : ∀ j : Fin q, Set.InjOn f (Flower.petal q a M j) :=
    fun j => (injOn_ball hb).mono (hball j)
  have hsc : ∀ j : Fin q, SimplyConnectedSpace (Flower.petal q a M j) :=
    fun j => flower_petal_simplyConnected hMpos hgeo j
  refine ⟨fun i => Flower.petal q a M i, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hgeo.isOpen_petal i, hgeo.isConnected_petal i, hsc i,
      fun z hz => hb.hsub (hball i hz)⟩
  · intro i z hz
    exact hmaps i hz
  · intro i j hij
    exact hgeo.disjoint_petal i j hij
  · intro i
    exact hgeo.zero_mem_closure_petal i
  · intro i
    exact hinj i

end Work.Horn

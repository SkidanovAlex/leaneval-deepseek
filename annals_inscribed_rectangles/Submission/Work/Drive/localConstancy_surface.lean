import Mathlib
import Submission.Work.Drive.localConstancy_oneThree

/-!
# Local constancy of a `1 + 1` meet count in a surface: the analytic core of `hn4` of the route

The chain route's side function is the **mod-2 surface count**

> `b u = ⟨#(A_u ⋔ C_0), 1⟩`,  `A_u = P_0 ∩ V_u` the *cut* of the reference plane `P_0` by the radial
> sweep `V_u`, `C_0 ⊂ P_0` the essential loop of `P_0` (a projective line)

(`Submission/Work/Drive/CUT_TRANSPORT_DESIGN.md` §1).  Both `A_u` and `C_0` are **`1`-cycles of the
surface `P_0 ≅ ℝP²`**, so this is a `1 + 1` count in dimension `2`.  The remaining hypothesis of the
count interface `Work.Drive.parityCore_of_countOnZc` is its **local constancy**

> `hn4 : ∀ x : Zc γ, ∀ᶠ y in 𝓝 x, n 0 y = n 0 x`

(`Submission/Work/Drive/countInterfaceFix.lean`).  This file supplies the analytic engine that turns a
presentation of the cut as a *smooth family of closed curves* into that local constancy.

## What is here

* `Work.Drive.meetS L D` — the **meet set** of a `1`-periodic loop `L` and a `1`-periodic curve `D`,
  in the fundamental domains: `{(t,v) | t ∈ [0,1), v ∈ [0,1), L t = D v}`.  Its cardinality is the
  number of intersection points of the two curves (when they are transverse), i.e. the count above.
* **`Work.Drive.eventually_meetS_cover`** — the compactness half: for `s → 0` every meet point of
  `D s` is close to a meet point of `D 0`.  (The periodicity of `L` and `D` is used exactly at the
  seam `t = 1` / `v = 1`: a meet point running to a seam has an interior translate at `s = 0`, which
  the interiority hypothesis rules out.)
* **`Work.Drive.eventually_ncard_meetS_eq`** — the engine: if the meet points of `D 0` are *interior*
  (in the open parameter square) and *regular* (the two tangent directions at a meet point are
  independent: `fderiv ℝ (L · − D 0 ·)` is surjective, so the system is transverse), then the *number*
  of meet points is **constant** for `s` near `0`.  In particular its parity is locally constant.

The proof is the standard three-step argument, on the template of
`Work.Drive.locallyConstant_labelMeet_eq`: the local solutions of the regular family (the square case of
the implicit function theorem, `Work.Drive.exists_local_solution_of_surjective`), their separation by a
radius coming from finiteness of the meet set at `s = 0`, and the compactness cover.  No homology, no
Sard: the regularity hypothesis is *given*, at the single parameter `s = 0`.

## The remaining items (stated for the fleet in the delegation notes)

* the same statement for a **finite system** of curves (the cut of the route has several components),
  `Work.Drive.eventually_ncard_meetSystem_eq`;
* the same statement for a loop and a family of curves in a **charted `2`-manifold** (the surface
  `P_0` in the capping space is not a vector space), `Work.Drive.eventually_ncard_meetManifold_eq`;
* finiteness of the meet set from regularity (the `hfin` hypothesis below, removable),
  `Work.Drive.finite_meetS_of_regular`.
-/

namespace Work.Drive

open Filter
open scoped Topology ContDiff

noncomputable section

/-! ## 1. The meet set of a loop and a family of curves -/

/-- **The meet set of a `1`-periodic loop `L` and a `1`-periodic curve `D`**: the pairs of parameters
in the fundamental domains `[0,1)` whose images agree.  Its cardinality is the intersection count of
the two curves (when they are transverse). -/
def meetS {E : Type*} (L D : ℝ → E) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Ico (0 : ℝ) 1 ∧ p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ L p.1 = D p.2}

@[simp] lemma mem_meetS {E : Type*} {L D : ℝ → E} {p : ℝ × ℝ} :
    p ∈ meetS L D ↔ p.1 ∈ Set.Ico (0 : ℝ) 1 ∧ p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ L p.1 = D p.2 :=
  Iff.rfl

lemma meetS_eq_iff {E : Type*} [AddGroup E] {L D : ℝ → E} {p : ℝ × ℝ} :
    p ∈ meetS L D ↔ p.1 ∈ Set.Ico (0 : ℝ) 1 ∧ p.2 ∈ Set.Ico (0 : ℝ) 1 ∧
      L p.1 - D p.2 = 0 := by
  rw [mem_meetS, sub_eq_zero]

/-- **The meet set of a loop and a *finite system* of curves**, indexed so that the fibres over the
index are disjoint.  The cut of the route has several components, and this is the set whose
cardinality is the total number of meets. -/
def meetSystem {E : Type*} {ι : Type*} (L : ℝ → E) (D : ι → ℝ → E) : Set (ι × ℝ × ℝ) :=
  {p | p.2.1 ∈ Set.Ico (0 : ℝ) 1 ∧ p.2.2 ∈ Set.Ico (0 : ℝ) 1 ∧ L p.2.1 = D p.1 p.2.2}

@[simp] lemma mem_meetSystem {E ι : Type*} {L : ℝ → E} {D : ι → ℝ → E} {p : ι × ℝ × ℝ} :
    p ∈ meetSystem L D ↔ p.2.1 ∈ Set.Ico (0 : ℝ) 1 ∧ p.2.2 ∈ Set.Ico (0 : ℝ) 1 ∧
      L p.2.1 = D p.1 p.2.2 :=
  Iff.rfl

/-- The system meet set is the disjoint union of the meet sets of its curves, the index being carried in
the first coordinate. -/
lemma meetSystem_eq_iUnion {E : Type*} {ι : Type*} (L : ℝ → E) (D : ι → ℝ → E) :
    meetSystem L D = ⋃ i : ι, (fun p : ℝ × ℝ => ((i, p) : ι × ℝ × ℝ)) '' meetS L (D i) := by
  ext p
  constructor
  · intro hp
    exact Set.mem_iUnion.mpr ⟨p.1, p.2, ⟨hp.1, hp.2.1, hp.2.2⟩, rfl⟩
  · intro hp
    obtain ⟨i, q, hq, hqp⟩ := Set.mem_iUnion.mp hp
    rw [← hqp]
    exact mem_meetS.mp hq

lemma meetSystem_subset_iff {E : Type*} {ι : Type*} {L : ℝ → E} {D : ι → ℝ → E}
    {p : ι × ℝ × ℝ} : p ∈ meetSystem L D ↔ (p.2 ∈ meetS L (D p.1)) := Iff.rfl

/-! ## 2. The compactness cover -/

/-- **Upper semicontinuity of the meet set.**  Given a continuous family `(s,p) ↦ L p.1 − D s p.2` and
a positive radius `δ ξ` at every meet point `ξ` of `D 0`, all meet points of `D s` with `s` close to
`0` lie in the corresponding ball around a meet point of `D 0`.

The hypotheses `hLper`, `hDper` (periodicity) and `hint` (every meet point of `D 0` is *interior* in
the parameter square) are exactly what the seam `t = 1` costs: a meet point of `D s` running to the
seam `t = 1` has, at `s = 0`, an interior representative of the loop parameter which `hint` forbids.

This is the surface analogue of `Work.Drive.eventually_bdyZeros_cover`. -/
theorem eventually_meetS_cover {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ → E} {D : ℝ → ℝ → E}
    (hcont : Continuous (fun q : ℝ × (ℝ × ℝ) => L q.2.1 - D q.1 q.2.2))
    (hLper : ∀ t : ℝ, L (t + 1) = L t) (hDper : ∀ s v : ℝ, D s (v + 1) = D s v)
    (hint : ∀ p ∈ meetS L (D 0), p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ p.2 ∈ Set.Ioo (0 : ℝ) 1)
    {δ : meetS L (D 0) → ℝ} (hδ : ∀ ξ, 0 < δ ξ) :
    ∀ᶠ s in nhds (0 : ℝ), ∀ p ∈ meetS L (D s),
      ∃ ξ : meetS L (D 0), ‖p - ξ.1‖ < δ ξ := by
  have key : ∃ ε > 0, ∀ s, |s| < ε → ∀ p ∈ meetS L (D s),
      ∃ ξ : meetS L (D 0), ‖p - ξ.1‖ < δ ξ := by
    by_contra hcon
    push Not at hcon
    have hseq : ∀ k : ℕ, ∃ s : ℝ, ∃ p : ℝ × ℝ, |s| < 1 / ((k : ℝ) + 1) ∧
        p ∈ meetS L (D s) ∧ ∀ ξ : meetS L (D 0), δ ξ ≤ ‖p - ξ.1‖ := by
      intro k
      obtain ⟨s, hs, p, hp, hfar⟩ := hcon (1 / ((k : ℝ) + 1)) (by positivity)
      exact ⟨s, p, hs, hp, hfar⟩
    choose s p hs hp hfar using hseq
    have hst : Tendsto s atTop (nhds (0 : ℝ)) := by
      refine squeeze_zero_norm' (a := fun k : ℕ => 1 / ((k : ℝ) + 1)) ?_
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact Filter.Eventually.of_forall fun k => le_of_lt (hs k)
    have hpm : ∀ k, p k ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := fun k => by
      obtain ⟨ht, hv, -⟩ := mem_meetS.mp (hp k)
      exact ⟨⟨ht.1, le_of_lt ht.2⟩, ⟨hv.1, le_of_lt hv.2⟩⟩
    obtain ⟨a, ha, φ, hφ, hpt⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hpm
    have ha1 : 0 ≤ a.1 ∧ a.1 ≤ 1 := ha.1
    have ha2 : 0 ≤ a.2 ∧ a.2 ≤ 1 := ha.2
    have hpair : Tendsto (fun k : ℕ => (s (φ k), p (φ k))) atTop (nhds ((0 : ℝ), a)) :=
      (hst.comp hφ.tendsto_atTop).prodMk_nhds hpt
    have hzero : L a.1 - D 0 a.2 = 0 := by
      have h1 : Tendsto (fun k : ℕ => L (p (φ k)).1 - D (s (φ k)) (p (φ k)).2) atTop
          (nhds (L a.1 - D 0 a.2)) :=
        (hcont.continuousAt (x := ((0 : ℝ), a))).tendsto.comp hpair
      have h2 : Tendsto (fun k : ℕ => L (p (φ k)).1 - D (s (φ k)) (p (φ k)).2) atTop
          (nhds (0 : E)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards with k
        exact (sub_eq_zero.mpr (mem_meetS.mp (hp (φ k))).2.2).symm
      exact tendsto_nhds_unique h1 h2
    have hLa : L a.1 = D 0 a.2 := sub_eq_zero.mp hzero
    -- the limit point is interior in the parameter square
    have hlt : a.1 < 1 ∧ a.2 < 1 := by
      rcases lt_or_ge a.1 1 with h1 | h1
      · rcases lt_or_ge a.2 1 with h2 | h2
        · exact ⟨h1, h2⟩
        · -- `a.2 = 1`: the point `(·, 0)` is a meet point of `D 0` with a coordinate `0`
          have haeq : a.2 = 1 := le_antisymm ha2.2 h2
          set t' : ℝ := if a.1 = 1 then 0 else a.1 with ht'def
          have ht'Ico : t' ∈ Set.Ico (0 : ℝ) 1 := by
            by_cases h1' : a.1 = 1
            · simp [ht'def, h1']
            · have : t' = a.1 := by simp [ht'def, h1']
              rw [this]; exact ⟨ha1.1, lt_of_le_of_ne ha1.2 h1'⟩
          have ht'L : L t' = L a.1 := by
            by_cases h1' : a.1 = 1
            · have : t' = 0 := by simp [ht'def, h1']
              rw [this, h1']
              simpa using (hLper 0).symm
            · have : t' = a.1 := by simp [ht'def, h1']
              rw [this]
          have hmem : (t', 0) ∈ meetS L (D 0) := by
            refine ⟨ht'Ico, ⟨le_refl 0, zero_lt_one⟩, ?_⟩
            show L t' = D 0 0
            rw [ht'L, hLa, haeq]
            simpa using hDper 0 0
          have := (hint (t', 0) hmem).2
          exact absurd this.1 (by norm_num)
      · -- `a.1 = 1`: the point `(0, ·)` is a meet point of `D 0` with a coordinate `0`
        have haeq : a.1 = 1 := le_antisymm ha1.2 h1
        set v' : ℝ := if a.2 = 1 then 0 else a.2 with hv'def
        have hv'Ico : v' ∈ Set.Ico (0 : ℝ) 1 := by
          by_cases h2' : a.2 = 1
          · simp [hv'def, h2']
          · have : v' = a.2 := by simp [hv'def, h2']
            rw [this]; exact ⟨ha2.1, lt_of_le_of_ne ha2.2 h2'⟩
        have hv'D : D 0 v' = D 0 a.2 := by
          by_cases h2' : a.2 = 1
          · have : v' = 0 := by simp [hv'def, h2']
            rw [this, h2']
            simpa using (hDper 0 0).symm
          · have : v' = a.2 := by simp [hv'def, h2']
            rw [this]
        have hmem : (0, v') ∈ meetS L (D 0) := by
          refine ⟨⟨le_refl 0, zero_lt_one⟩, hv'Ico, ?_⟩
          show L 0 = D 0 v'
          rw [hv'D, ← hLa, haeq]
          simpa using (hLper 0).symm
        have := (hint (0, v') hmem).1
        exact absurd this.1 (by norm_num)
    have hamem : a ∈ meetS L (D 0) :=
      ⟨⟨ha1.1, hlt.1⟩, ⟨ha2.1, hlt.2⟩, hLa⟩
    have hfar' : ∀ k, δ ⟨a, hamem⟩ ≤ ‖p (φ k) - a‖ := fun k => by
      simpa using hfar (φ k) ⟨a, hamem⟩
    have hev : ∀ᶠ k in atTop, ‖p (φ k) - a‖ < δ ⟨a, hamem⟩ :=
      hpt.eventually (Metric.ball_mem_nhds a (hδ ⟨a, hamem⟩))
    obtain ⟨k, hk⟩ := hev.exists
    exact absurd hk (not_lt.mpr (hfar' k))
  obtain ⟨ε, hε, hval⟩ := key
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with s hs
  refine hval s ?_
  have : dist s 0 < ε := by simpa [Metric.mem_ball] using hs
  rwa [Real.dist_eq, sub_zero] at this

/-! ## 3. The engine: local constancy of the meet count -/

/-- **Local constancy of the number of meet points of a loop and a smooth family of curves.**

Let `L` and each `D s` be `1`-periodic (closed) curves of a normed space `E` of the same dimension as
the parameter square `ℝ × ℝ` (in the application `E` is the plane `ℝ²` or a chart of the surface), and
let `(s,p) ↦ L p.1 − D s p.2` be smooth.  Assume:

* `hfin` — the meet set of `D 0` is finite (it is the number of intersection points at `s = 0`);
* `hint` — every meet point of `D 0` is *interior* in the parameter square (so it survives the
  periodic identification; this is the standing hypothesis under which the seam count is unaffected);
* `hreg` — every meet point of `D 0` is *regular*: the derivative of the difference map there is
  surjective; the parameter square and `E` having the same dimension, this is the **transversality** of
  the loop and the curve at the meet point.

Then the number of meet points is constant for `s` near `0`; in particular its parity (the mod-2
intersection number of the two curves) is locally constant. -/
theorem eventually_ncard_meetS_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L : ℝ → E) (D : ℝ → ℝ → E)
    (hL : ContDiff ℝ Ctop L) (hLper : ∀ t : ℝ, L (t + 1) = L t)
    (hD : ContDiff ℝ Ctop (fun q : ℝ × ℝ => D q.1 q.2))
    (hDper : ∀ s v : ℝ, D s (v + 1) = D s v)
    (hfin : (meetS L (D 0)).Finite)
    (hint : ∀ p ∈ meetS L (D 0), p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ p.2 ∈ Set.Ioo (0 : ℝ) 1)
    (hdim : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ E)
    (hreg : ∀ p ∈ meetS L (D 0),
      Function.Surjective (fderiv ℝ (fun q : ℝ × ℝ => L q.1 - D 0 q.2) p)) :
    ∀ᶠ s in nhds (0 : ℝ), (meetS L (D s)).ncard = (meetS L (D 0)).ncard := by
  classical
  have hG : ContDiff ℝ Ctop (fun q : ℝ × (ℝ × ℝ) => L q.2.1 - D q.1 q.2.2) := by fun_prop
  haveI : Finite (meetS L (D 0)) := hfin.to_subtype
  haveI : Fintype (meetS L (D 0)) := hfin.fintype
  -- the local solution at each meet point of `D 0`
  have hloc : ∀ ξ : meetS L (D 0), ∃ (ε δ : ℝ) (ψ : ℝ → ℝ × ℝ), 0 < ε ∧ 0 < δ ∧ ψ 0 = ξ.1 ∧
      Tendsto ψ (nhds (0 : ℝ)) (nhds ξ.1) ∧
      (∀ s, |s| < ε → ‖ψ s - ξ.1‖ < δ ∧ L (ψ s).1 - D s (ψ s).2 = 0) ∧
      (∀ s, |s| < ε → ∀ x, ‖x - ξ.1‖ < δ → L x.1 - D s x.2 = 0 → x = ψ s) := by
    intro ξ
    have hξ0 : (fun q : ℝ × ℝ => L q.1 - D 0 q.2) ξ.1 = 0 := sub_eq_zero.mpr ξ.2.2.2
    exact exists_local_solution_of_surjective (fun s q => L q.1 - D s q.2) hG hdim hξ0
      (hreg ξ.1 ξ.2)
  choose ε₀ δ₀ ψ₀ hε₀ hδ₀ hψ₀ hcont₀ hmain₀ huniq₀ using hloc
  -- separation radius of the (finite) meet set of `D 0`
  obtain ⟨ρ, hρpos, hρ⟩ := exists_pos_le_dist_of_finite hfin
  -- a radius inside the open parameter square at each meet point
  have hff : ∀ ξ : meetS L (D 0), ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ × ℝ, ‖x - ξ.1‖ < r →
      x.1 ∈ Set.Ico (0 : ℝ) 1 ∧ x.2 ∈ Set.Ico (0 : ℝ) 1 := by
    intro ξ
    obtain ⟨ht, hv⟩ := hint ξ.1 ξ.2
    set m : ℝ := min (ξ.1.1) (min (1 - ξ.1.1) (min (ξ.1.2) (1 - ξ.1.2))) with hmdef
    have hmpos : 0 < m := by
      rw [hmdef]
      exact lt_min ht.1 (lt_min (by linarith [ht.2]) (lt_min hv.1 (by linarith [hv.2])))
    refine ⟨m / 2, by linarith, ?_⟩
    intro x hx
    have hm1 : m ≤ ξ.1.1 := by rw [hmdef]; exact min_le_left _ _
    have hm2 : m ≤ 1 - ξ.1.1 := by
      rw [hmdef]; exact (min_le_right _ _).trans (min_le_left _ _)
    have hm3 : m ≤ ξ.1.2 := by
      rw [hmdef]; exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
    have hm4 : m ≤ 1 - ξ.1.2 := by
      rw [hmdef]; exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
    have hr1 : m / 2 ≤ ξ.1.1 := (half_le_self (le_of_lt hmpos)).trans hm1
    have hr2 : m / 2 ≤ 1 - ξ.1.1 := (half_le_self (le_of_lt hmpos)).trans hm2
    have hr3 : m / 2 ≤ ξ.1.2 := (half_le_self (le_of_lt hmpos)).trans hm3
    have hr4 : m / 2 ≤ 1 - ξ.1.2 := (half_le_self (le_of_lt hmpos)).trans hm4
    have hb1 : |x.1 - ξ.1.1| < m / 2 := by
      have h := lt_of_le_of_lt (norm_fst_le (x - ξ.1)) hx
      simpa using h
    have hb2 : |x.2 - ξ.1.2| < m / 2 := by
      have h := lt_of_le_of_lt (norm_snd_le (x - ξ.1)) hx
      simpa using h
    have hb1' := abs_lt.mp hb1
    have hb2' := abs_lt.mp hb2
    exact ⟨⟨by linarith [hb1'.1, hr1], by linarith [hb1'.2, hr2]⟩,
      ⟨by linarith [hb2'.1, hr3], by linarith [hb2'.2, hr4]⟩⟩
  choose rf hrfpos hrf using hff
  set δZ : meetS L (D 0) → ℝ := fun ξ => min (δ₀ ξ) (min (rf ξ) ρ) with hδZdef
  have hδZval : ∀ ξ, δZ ξ = min (δ₀ ξ) (min (rf ξ) ρ) := fun ξ => rfl
  have hδZpos : ∀ ξ, 0 < δZ ξ := by
    intro ξ; rw [hδZval]; exact lt_min (hδ₀ ξ) (lt_min (hrfpos ξ) hρpos)
  have hδZ_le_δ₀ : ∀ ξ, δZ ξ ≤ δ₀ ξ := fun ξ =>
    (le_of_eq (hδZval ξ)).trans (min_le_left _ _)
  have hδZ_le_rf : ∀ ξ, δZ ξ ≤ rf ξ := fun ξ =>
    (le_of_eq (hδZval ξ)).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδZ_le_ρ : ∀ ξ, δZ ξ ≤ ρ := fun ξ =>
    (le_of_eq (hδZval ξ)).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the three eventual statements
  have hevA : ∀ᶠ s in nhds (0 : ℝ), ∀ ξ : meetS L (D 0),
      ‖ψ₀ ξ s - ξ.1‖ < δZ ξ ∧ L (ψ₀ ξ s).1 - D s (ψ₀ ξ s).2 = 0 := by
    rw [Filter.eventually_all]
    intro ξ
    have h1 : ∀ᶠ s in nhds (0 : ℝ), |s| < ε₀ ξ := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (hε₀ ξ)] with s hs
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
      exact hs
    have h2 : ∀ᶠ s in nhds (0 : ℝ), ‖ψ₀ ξ s - ξ.1‖ < δZ ξ := by
      have hc := (hcont₀ ξ).eventually (Metric.ball_mem_nhds ξ.1 (hδZpos ξ))
      filter_upwards [hc] with s hs
      simpa [dist_eq_norm] using hs
    filter_upwards [h1, h2] with s hs1 hs2
    exact ⟨hs2, (hmain₀ ξ s hs1).2⟩
  have hevB : ∀ᶠ s in nhds (0 : ℝ), ∀ p ∈ meetS L (D s),
      ∃ ξ : meetS L (D 0), ‖p - ξ.1‖ < δZ ξ :=
    eventually_meetS_cover hG.continuous hLper hDper hint hδZpos
  have hevC : ∀ᶠ s in nhds (0 : ℝ), ∀ ξ : meetS L (D 0), ∀ x : ℝ × ℝ, ‖x - ξ.1‖ < δZ ξ →
      L x.1 - D s x.2 = 0 → x = ψ₀ ξ s := by
    rw [Filter.eventually_all]
    intro ξ
    have h1 : ∀ᶠ s in nhds (0 : ℝ), |s| < ε₀ ξ := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (hε₀ ξ)] with s hs
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
      exact hs
    filter_upwards [h1] with s hs1 x hx hx0
    exact huniq₀ ξ s hs1 x (lt_of_lt_of_le hx (hδZ_le_δ₀ ξ)) hx0
  filter_upwards [hevA, hevB, hevC] with s hA hB hC
  -- the parametrisation of the meet set of `D s` by that of `D 0`
  set Ψ : meetS L (D 0) → ℝ × ℝ := fun ξ => ψ₀ ξ s with hΨdef
  have hΨmem : ∀ ξ : meetS L (D 0), Ψ ξ ∈ meetS L (D s) := by
    intro ξ
    have hfr := hrf ξ (Ψ ξ) (lt_of_lt_of_le (hA ξ).1 (hδZ_le_rf ξ))
    exact ⟨hfr.1, hfr.2, sub_eq_zero.mp (hA ξ).2⟩
  have hΨinj : Function.Injective Ψ := by
    intro ξ η hξη
    by_contra hne
    have hd : ξ.1 ≠ η.1 := fun h => hne (Subtype.ext h)
    have h1 : ‖Ψ ξ - ξ.1‖ < δZ ξ := (hA ξ).1
    have h2 : ‖Ψ η - η.1‖ < δZ η := (hA η).1
    have h3 : 2 * ρ ≤ ‖ξ.1 - η.1‖ := hρ ξ.1 ξ.2 η.1 η.2 hd
    have h4 : ‖ξ.1 - η.1‖ ≤ ‖Ψ ξ - ξ.1‖ + ‖Ψ η - η.1‖ := by
      have hsub : ξ.1 - η.1 = (ξ.1 - Ψ ξ) + (Ψ ξ - η.1) := by abel
      calc ‖ξ.1 - η.1‖ = ‖(ξ.1 - Ψ ξ) + (Ψ ξ - η.1)‖ := by rw [hsub]
        _ ≤ ‖ξ.1 - Ψ ξ‖ + ‖Ψ ξ - η.1‖ := norm_add_le _ _
        _ = ‖Ψ ξ - ξ.1‖ + ‖Ψ η - η.1‖ := by rw [norm_sub_rev, hξη]
    have h5 : δZ ξ + δZ η ≤ 2 * ρ := by linarith [hδZ_le_ρ ξ, hδZ_le_ρ η]
    linarith
  have hΨval : ∀ ξ : meetS L (D 0), Ψ ξ = ψ₀ ξ s := fun ξ => rfl
  have hΨsurj : ∀ x ∈ meetS L (D s), ∃ ξ : meetS L (D 0), Ψ ξ = x := by
    intro x hx
    obtain ⟨ξ, hdist⟩ := hB x hx
    refine ⟨ξ, ?_⟩
    rw [hΨval ξ]
    exact (hC ξ x hdist (sub_eq_zero.mpr hx.2.2)).symm
  -- the meet set of `D s` is in bijection with the meet set of `D 0`
  let Φ : meetS L (D 0) → meetS L (D s) := fun ξ => ⟨Ψ ξ, hΨmem ξ⟩
  have hΦinj : Function.Injective Φ := by
    intro ξ η h
    exact hΨinj (congrArg Subtype.val h)
  have hΦsurj : Function.Surjective Φ := by
    intro x
    obtain ⟨ξ, hξ⟩ := hΨsurj x.1 x.2
    exact ⟨ξ, Subtype.ext hξ⟩
  have hcard : Nat.card (meetS L (D s)) = Nat.card (meetS L (D 0)) :=
    Nat.card_congr (Equiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩).symm
  have hfinS : Finite (meetS L (D s)) := Finite.of_surjective Φ hΦsurj
  have hfS : (meetS L (D s)).Finite := Set.finite_coe_iff.mp hfinS
  haveI : Fintype (meetS L (D s)) := hfS.fintype
  have hA : (meetS L (D s)).ncard = Nat.card (meetS L (D s)) := by
    rw [Set.ncard_eq_toFinset_card _ hfS, hfS.card_toFinset, Fintype.card_eq_nat_card]
  have hB' : (meetS L (D 0)).ncard = Nat.card (meetS L (D 0)) := by
    rw [Set.ncard_eq_toFinset_card _ hfin, hfin.card_toFinset, Fintype.card_eq_nat_card]
  exact hA.trans (hcard.trans hB'.symm)

/-- **The mod-2 form of the engine.**  *Scope warning*: in a **plane** the parity of the meet count of
two closed curves is *always* even (their mod-2 intersection number vanishes in a simply connected
surface; this is `Work.Drive.even_ncard_closed_curves_meet`, proved in this workspace with exactly the
hypotheses used here), so this corollary is *uninformative* in the plane: every configuration
satisfying the hypotheses has an even meet count, and the conclusion holds without any deformation
argument.  The content of `eventually_ncard_meetS_eq` is the *integer* constancy of the count (which can
jump from `2` to `4` only across a non-transversal configuration).  The count of the chain route is a
count in a *surface* (two projective lines of `ℝP²` meet exactly once), for which the route must use
the homological argument or the arc decomposition of the cut — see
`Submission/Work/Drive/SURFACE_COUNT_LOCALITY_STATUS.md` §2.6 and §5bis. -/
theorem eventually_even_ncard_meetS_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L : ℝ → E) (D : ℝ → ℝ → E)
    (hL : ContDiff ℝ Ctop L) (hLper : ∀ t : ℝ, L (t + 1) = L t)
    (hD : ContDiff ℝ Ctop (fun q : ℝ × ℝ => D q.1 q.2))
    (hDper : ∀ s v : ℝ, D s (v + 1) = D s v)
    (hfin : (meetS L (D 0)).Finite)
    (hint : ∀ p ∈ meetS L (D 0), p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ p.2 ∈ Set.Ioo (0 : ℝ) 1)
    (hdim : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ E)
    (hreg : ∀ p ∈ meetS L (D 0),
      Function.Surjective (fderiv ℝ (fun q : ℝ × ℝ => L q.1 - D 0 q.2) p)) :
    ∀ᶠ s in nhds (0 : ℝ),
      ((meetS L (D s)).ncard + (meetS L (D 0)).ncard) % 2 = 0 := by
  filter_upwards [eventually_ncard_meetS_eq L D hL hLper hD hDper hfin hint hdim hreg]
    with s hs
  rw [hs]
  omega

/-- **The `ZMod 2`-valued form of the engine.**  Same scope warning as
`eventually_even_ncard_meetS_eq`: in a plane the value is always `0` (the meet count of two closed
curves of a plane is even), so this is *not* the statement the route needs for the side function `b u`,
whose count takes odd values in the surface `P_0 ≅ ℝP²`. -/
theorem eventually_zmod2_ncard_meetS_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L : ℝ → E) (D : ℝ → ℝ → E)
    (hL : ContDiff ℝ Ctop L) (hLper : ∀ t : ℝ, L (t + 1) = L t)
    (hD : ContDiff ℝ Ctop (fun q : ℝ × ℝ => D q.1 q.2))
    (hDper : ∀ s v : ℝ, D s (v + 1) = D s v)
    (hfin : (meetS L (D 0)).Finite)
    (hint : ∀ p ∈ meetS L (D 0), p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ p.2 ∈ Set.Ioo (0 : ℝ) 1)
    (hdim : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ E)
    (hreg : ∀ p ∈ meetS L (D 0),
      Function.Surjective (fderiv ℝ (fun q : ℝ × ℝ => L q.1 - D 0 q.2) p)) :
    ∀ᶠ s in nhds (0 : ℝ),
      (((meetS L (D s)).ncard : ℕ) : ZMod 2) = (((meetS L (D 0)).ncard : ℕ) : ZMod 2) := by
  filter_upwards [eventually_ncard_meetS_eq L D hL hLper hD hDper hfin hint hdim hreg]
    with s hs
  rw [hs]

/-- **The count may be computed in a chart.**  If two curves of a surface are presented in the
coordinates of a chart `e` of the surface (their coordinate expressions `L'`, `D'` taking values in the
chart's target), then the meet set of the curves in the surface is in bijection with the meet set of
their coordinate expressions, so the two counts agree.  This is what lets the engine, which is stated
for curves of a normed plane, be used for the concrete cut of the route: the transport lane presents
the cut and the core in coordinates. -/
theorem ncard_meetS_chart {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (L' D' : ℝ → EuclideanSpace ℝ (Fin 2)) (hL : Set.range L' ⊆ e.target)
    (hD : Set.range D' ⊆ e.target) :
    (meetS (fun t : ℝ => e.symm (L' t)) (fun v : ℝ => e.symm (D' v))).ncard
      = (meetS L' D').ncard := by
  congr 1
  ext p
  rw [mem_meetS, mem_meetS]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have h1' := congrArg e h3
    rw [e.right_inv (hL (Set.mem_range_self p.1)),
      e.right_inv (hD (Set.mem_range_self p.2))] at h1'
    exact ⟨h1, h2, h1'⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rw [h3]⟩

/-- The dimension hypothesis of the engine in the shape in which it is discharged for the plane: the
parameter square and the Euclidean plane have the same dimension. -/
lemma finrank_prod_eq_finrank_euclideanSpace_two :
    Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by
  rw [Module.finrank_prod, finrank_euclideanSpace]
  simp

/-- **The engine in the coordinates of a chart of a surface** — the form in which the chain route
consumes it.  The surface `P_0` is presented by a chart `e`; the core and the cut are given by their
coordinate expressions `L'`, `D' s` (whose values lie in the chart's target).  Under the engine's
hypotheses on the coordinate curves, the number of meets of the core with the cut is constant for `s`
near `0`. -/
theorem eventually_ncard_meetS_chart_eq {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (L' : ℝ → EuclideanSpace ℝ (Fin 2)) (D' : ℝ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hL : ∀ t : ℝ, L' t ∈ e.target) (hD : ∀ s v : ℝ, D' s v ∈ e.target)
    (hLs : ContDiff ℝ Ctop L') (hLper : ∀ t : ℝ, L' (t + 1) = L' t)
    (hDs : ContDiff ℝ Ctop (fun q : ℝ × ℝ => D' q.1 q.2))
    (hDper : ∀ s v : ℝ, D' s (v + 1) = D' s v)
    (hfin : (meetS L' (D' 0)).Finite)
    (hint : ∀ p ∈ meetS L' (D' 0), p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ p.2 ∈ Set.Ioo (0 : ℝ) 1)
    (hreg : ∀ p ∈ meetS L' (D' 0),
      Function.Surjective (fderiv ℝ (fun q : ℝ × ℝ => L' q.1 - D' 0 q.2) p)) :
    ∀ᶠ s in nhds (0 : ℝ),
      (meetS (fun t : ℝ => e.symm (L' t)) (fun v : ℝ => e.symm (D' s v))).ncard
        = (meetS (fun t : ℝ => e.symm (L' t)) (fun v : ℝ => e.symm (D' 0 v))).ncard := by
  filter_upwards [eventually_ncard_meetS_eq L' D' hLs hLper hDs hDper hfin hint
    finrank_prod_eq_finrank_euclideanSpace_two hreg] with s hs
  rw [ncard_meetS_chart e L' (D' s) (Set.range_subset_iff.mpr hL)
      (Set.range_subset_iff.mpr fun v => hD s v), hs,
    ncard_meetS_chart e L' (D' 0) (Set.range_subset_iff.mpr hL)
      (Set.range_subset_iff.mpr fun v => hD 0 v)]

end

end Work.Drive

import Mathlib
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.L.MaxDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 2000000

/-!
# Maximal Ricci flow (dichotomy)

`Work.Diff.L.maximal_flow_v3`: from a metric `g₀` whose curvature lies in an invariant set `F`,
either there are Ricci flows starting at `g₀` with curvature in `F` on `[0, T)` for **every**
`T > 0`, or there is a maximal flow whose curvature is **unbounded** on `[0, T)`.

The proof is the standard Zorn argument.  The pieces are

* `isRicciFlow_mono` : restricting a Ricci flow to a shorter interval;
* `static_family_const` : a static invariant set is an invariant family (needed to apply the
  maximum principle `PinchingPreserved` to a static set);
* `chain_upper_bound` : the union of a chain of flow packages (with bounded existence times) is a
  flow package above the whole chain — the chain condition of Zorn's lemma;
* the assembly, in which a maximal package either has unbounded curvature (second alternative) or
  is extended by `hEXT` (with the curvature staying in `F` by `hPP`), contradicting maximality.
-/

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]

/-! ## Restriction of a Ricci flow -/

/-- A Ricci flow on `[0, T')` is a Ricci flow on `[0, T)` for every `T ≤ T'`. -/
lemma isRicciFlow_mono {G : ℝ → SMet I M} {T T' : ℝ} (h : IsRicciFlow G T') (hTT : T ≤ T') :
    IsRicciFlow G T := by
  have hsub : Set.Ico 0 T ⊆ Set.Ico 0 T' := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hTT⟩
  refine ⟨h.1.mono (Set.prod_mono hsub Subset.rfl), fun t ht x u v => ?_⟩
  exact (h.2 t (hsub ht) x u v).mono hsub

/-! ## Static invariant sets are invariant families -/

/-- A static invariant set is an invariant family: the only content is the time shift in the
`ODEInvariant`/`ODEInvariantFamily` pair. -/
lemma static_family_const {n : ℕ} {F : Set (Curv4 n)} (hF : IsInvariantSet F) :
    IsInvariantFamily (fun _ : ℝ => F) := by
  obtain ⟨hcl, hcvx, halg, hrot, hode⟩ := hF
  refine ⟨?_, fun _ => hcvx, fun _ => halg, fun _ => hrot, ?_⟩
  · have hset : {p : ℝ × Curv4 n | p.2 ∈ F} = Set.univ ×ˢ F := by
      ext p; simp
    rw [hset]
    exact isClosed_univ.prod hcl
  · intro t₀ T R hR0 hderiv t ht
    have hst : Set.MapsTo (fun s : ℝ => t₀ + s) (Set.Ico 0 (T - t₀)) (Set.Ico t₀ T) := by
      intro s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hderiv' : ∀ s ∈ Set.Ico 0 (T - t₀),
        HasDerivWithinAt (fun s : ℝ => R (t₀ + s)) (Q (R (t₀ + s)))
          (Set.Ico 0 (T - t₀)) s := by
      intro s hs
      have h2 : HasDerivWithinAt (fun s : ℝ => t₀ + s) (1 : ℝ) (Set.Ico 0 (T - t₀)) s :=
        ((hasDerivAt_id s).const_add t₀).hasDerivWithinAt
      have h1 := (hderiv (t₀ + s) (hst hs)).scomp s h2 hst
      simpa [Function.comp_def, one_smul] using h1
    have hmem := hode (T - t₀) (fun s => R (t₀ + s)) (by simpa using hR0) hderiv' (t - t₀)
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hid : t₀ + (t - t₀) = t := by ring
    simpa [hid] using hmem

/-! ## The union of a chain of flow packages -/

/-- **Chain condition for Zorn.**  The union of a nonempty chain of flow packages with bounded
existence times is again a flow package, and it extends every member of the chain.  (The flow is
defined by choosing any member of the chain that exists past the given time; the chain condition
makes the choice irrelevant, and smoothness/derivative assertions are local.) -/
lemma chain_upper_bound {g₀ : SMet I M} {F : Set (Curv4 (Module.finrank ℝ E))}
    (c : Set (FlowPackage g₀ F)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hbdd : ∃ T₀ : ℝ, ∀ p ∈ c, p.1.1 ≤ T₀) :
    ∃ ub : FlowPackage g₀ F, ∀ z ∈ c, z ≤ ub := by
  classical
  obtain ⟨T₀, hT₀⟩ := hbdd
  have hSne : ({r : ℝ | ∃ p ∈ c, p.1.1 = r}).Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨p.1.1, p, hp, rfl⟩
  have hSbdd : BddAbove {r : ℝ | ∃ p ∈ c, p.1.1 = r} :=
    ⟨T₀, by rintro r ⟨p, hp, rfl⟩; exact hT₀ p hp⟩
  set Tstar : ℝ := sSup {r : ℝ | ∃ p ∈ c, p.1.1 = r} with hTstar
  have hlt : ∀ t : ℝ, t < Tstar → ∃ p ∈ c, t < p.1.1 := by
    intro t ht
    obtain ⟨r, ⟨p, hp, hr⟩, htr⟩ := (lt_csSup_iff hSbdd hSne).mp ht
    exact ⟨p, hp, by rw [hr]; exact htr⟩
  let G : ℝ → SMet I M := fun t =>
    if h : ∃ p ∈ c, t < p.1.1 then (Classical.choose h).1.2 t else g₀
  have hG_apply : ∀ t, G t = if h : ∃ p ∈ c, t < p.1.1 then
      (Classical.choose h).1.2 t else g₀ := fun t => rfl
  have hG_eq : ∀ z ∈ c, ∀ t ∈ Set.Ico 0 z.1.1, G t = z.1.2 t := by
    intro z hz t ht
    have hex : ∃ p ∈ c, t < p.1.1 := ⟨z, hz, ht.2⟩
    have hspec := Classical.choose_spec hex
    have hGt : G t = (Classical.choose hex).1.2 t := by
      rw [hG_apply t, dif_pos hex]
    rw [hGt]
    rcases eq_or_ne (Classical.choose hex) z with h | h
    · rw [h]
    · rcases hc hspec.1 hz h with hle | hle
      · exact (hle.2 t ⟨ht.1, hspec.2⟩).symm
      · exact hle.2 t ht
  have hpos : 0 < Tstar := by
    obtain ⟨p, hp⟩ := hne
    exact lt_of_lt_of_le p.2.1 (le_csSup hSbdd ⟨p, hp, rfl⟩)
  have hflowG : IsRicciFlow G Tstar := by
    refine ⟨?_, ?_⟩
    · apply contMDiffOn_of_locally_contMDiffOn
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      obtain ⟨p, hp, hpt⟩ := hlt t ht.2
      refine ⟨Set.Iio p.1.1 ×ˢ Set.univ, isOpen_Iio.prod isOpen_univ,
        ⟨hpt, mem_univ x⟩, ?_⟩
      have hsub : (Set.Ico 0 Tstar ×ˢ (Set.univ : Set M)) ∩ (Set.Iio p.1.1 ×ˢ (Set.univ : Set M))
          ⊆ Set.Ico 0 p.1.1 ×ˢ (Set.univ : Set M) := by
        rintro ⟨s, y⟩ ⟨⟨hs1, -⟩, hs2, -⟩
        exact ⟨⟨hs1.1, hs2⟩, mem_univ y⟩
      refine (p.2.2.1.1.mono hsub).congr ?_
      rintro ⟨s, y⟩ ⟨⟨hs1, -⟩, hs2, -⟩
      rw [hG_eq p hp s ⟨hs1.1, hs2⟩]
    · intro t ht x u v
      obtain ⟨p, hp, hpt⟩ := hlt t ht.2
      have hGt : G t = p.1.2 t := hG_eq p hp t ⟨ht.1, hpt⟩
      have hpp : p.1.1 ≤ Tstar := le_csSup hSbdd ⟨p, hp, rfl⟩
      -- the two time intervals agree in a neighbourhood of `t`
      have hset : Set.Ico 0 p.1.1 =ᶠ[𝓝 t] Set.Ico 0 Tstar := by
        filter_upwards [isOpen_Iio.mem_nhds hpt] with s hs
        exact propext ⟨fun h => ⟨h.1, lt_of_lt_of_le h.2 hpp⟩, fun h => ⟨h.1, hs⟩⟩
      have hpder : HasDerivWithinAt (fun s : ℝ => (p.1.2 s).inner x u v)
          (-2 * ricAt (lcOf (p.1.2 t)) x u v) (Set.Ico 0 Tstar) t :=
        (hasDerivWithinAt_congr_set hset).mp (p.2.2.1.2 t ⟨ht.1, hpt⟩ x u v)
      have hev : (fun s : ℝ => (G s).inner x u v) =ᶠ[𝓝[Set.Ico 0 Tstar] t]
          (fun s : ℝ => (p.1.2 s).inner x u v) := by
        have hmem : (Set.Ico 0 Tstar ∩ Set.Iio p.1.1) ∈ 𝓝[Set.Ico 0 Tstar] t :=
          Filter.inter_mem self_mem_nhdsWithin
            (mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds hpt))
        filter_upwards [hmem] with s hs
        rw [hG_eq p hp s ⟨hs.1.1, hs.2⟩]
      have hx : (G t).inner x u v = (p.1.2 t).inner x u v := by rw [hGt]
      rw [hGt]
      exact hpder.congr_of_eventuallyEq hev hx
  have hinitG : G 0 = g₀ := by
    obtain ⟨p, hp⟩ := hne
    have h0 := hG_eq p hp 0 ⟨le_refl 0, p.2.1⟩
    rw [h0, p.2.2.2.1]
  have hcurvG : ∀ t ∈ Set.Ico 0 Tstar, CurvIn (G t) F := by
    intro t ht
    obtain ⟨p, hp, hpt⟩ := hlt t ht.2
    rw [hG_eq p hp t ⟨ht.1, hpt⟩]
    exact p.2.2.2.2 t ⟨ht.1, hpt⟩
  have hpkg : IsFlowPackage g₀ F (Tstar, G) := ⟨hpos, hflowG, hinitG, hcurvG⟩
  refine ⟨⟨(Tstar, G), hpkg⟩, fun z hz => ⟨?_, fun t ht => hG_eq z hz t ht⟩⟩
  exact le_csSup hSbdd ⟨z, hz, rfl⟩

/-! ## The dichotomy -/

theorem maximal_flow_v3
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hSTE : Submission.Diff.ShortTimeExistence I M) (hEXT : Submission.Diff.Extension I M)
    (hPP : Submission.Diff.PinchingPreserved I M)
    (g₀ : Submission.Diff.SMet I M)
    (F : Set (Submission.Diff.Alg.Curv4 (Module.finrank ℝ E)))
    (hF : Submission.Diff.Alg.IsInvariantSet F) (hF0 : Submission.Diff.CurvIn g₀ F) :
    (∀ T : ℝ, 0 < T → ∃ G : ℝ → Submission.Diff.SMet I M,
        Submission.Diff.IsRicciFlow G T ∧ G 0 = g₀ ∧
          ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvIn (G t) F)
      ∨ (∃ T : ℝ, 0 < T ∧ ∃ G : ℝ → Submission.Diff.SMet I M,
        Submission.Diff.IsRicciFlow G T ∧ G 0 = g₀ ∧
          (∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvIn (G t) F) ∧
        ¬ (∃ C : ℝ, ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)) := by
  classical
  -- a flow package exists at short time, with curvature in `F` by the maximum principle
  obtain ⟨T₁, hT₁, G₁, hflow₁, hinit₁⟩ := hSTE g₀
  have hcurv₁ : ∀ t ∈ Set.Ico 0 T₁, CurvIn (G₁ t) F :=
    hPP (fun _ : ℝ => F) (static_family_const hF) G₁ T₁ hflow₁ (by rw [hinit₁]; exact hF0)
  have hpkg₁ : IsFlowPackage g₀ F (T₁, G₁) := ⟨hT₁, hflow₁, hinit₁, hcurv₁⟩
  by_cases hcase : ∀ T : ℝ, ∃ p : FlowPackage g₀ F, T ≤ p.1.1
  · -- arbitrarily long existence: restrict a long flow to each finite interval
    left
    intro T hT
    obtain ⟨p, hp⟩ := hcase T
    refine ⟨p.1.2, isRicciFlow_mono p.2.2.1 hp, p.2.2.2.1, fun t ht => ?_⟩
    exact p.2.2.2.2 t ⟨ht.1, lt_of_lt_of_le ht.2 hp⟩
  · -- existence times are bounded above: take a maximal flow
    right
    obtain ⟨T₀, hT₀⟩ : ∃ T : ℝ, ∀ p : FlowPackage g₀ F, p.1.1 < T := by
      simpa only [not_forall, not_exists, not_le] using hcase
    have hmax : ∃ m : FlowPackage g₀ F, IsMax m := by
      apply zorn_le
      intro c hc
      rcases c.eq_empty_or_nonempty with hc0 | hne
      · subst hc0
        exact ⟨⟨(T₁, G₁), hpkg₁⟩, fun z hz => (Set.notMem_empty z hz).elim⟩
      · exact chain_upper_bound c hc hne ⟨T₀, fun p _ => le_of_lt (hT₀ p)⟩
    obtain ⟨m, hm⟩ := hmax
    by_cases hbnd : ∃ C : ℝ, ∀ t ∈ Set.Ico 0 m.1.1, CurvBound (m.1.2 t) C
    · -- bounded curvature on a maximal flow: `hEXT` extends it, contradicting maximality
      exfalso
      obtain ⟨C, hC⟩ := hbnd
      obtain ⟨T', hT', G', hflow', hG'⟩ := hEXT m.1.2 m.1.1 C m.2.1 m.2.2.1 hC
      have hG'0 : G' 0 = g₀ := by rw [hG' 0 ⟨le_refl 0, m.2.1⟩, m.2.2.2.1]
      have hcurv' : ∀ t ∈ Set.Ico 0 T', CurvIn (G' t) F :=
        hPP (fun _ : ℝ => F) (static_family_const hF) G' T' hflow' (by rw [hG'0]; exact hF0)
      have hnew : IsFlowPackage g₀ F (T', G') :=
        ⟨lt_trans m.2.1 hT', hflow', hG'0, hcurv'⟩
      have hle : m ≤ ⟨(T', G'), hnew⟩ := ⟨le_of_lt hT', fun t ht => hG' t ht⟩
      exact absurd (hm hle).1 (not_le.mpr hT')
    · -- a maximal flow with unbounded curvature
      exact ⟨m.1.1, m.2.1, m.1.2, m.2.2.1, m.2.2.2.1, m.2.2.2.2, hbnd⟩

end Work.Diff.L

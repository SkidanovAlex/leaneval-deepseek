import Mathlib
import Submission.Work.Smooth.SphereJordan.mobiusAddInv
import Submission.Work.Smooth.JordanSeparation.onePoint_locallyPathConnected

/-!
# Reduction of the sphere crux to the plane crux

Let `hplane` be the plane crux: for a closed, preconnected, unbounded `F ⊆ ℂ` every loop in `Fᶜ`
is null-homotopic.  Let `hsphere` be the simple-connectedness of the Riemann sphere `OnePoint ℂ`.

Given a compact preconnected `K ⊆ OnePoint ℂ` and a loop `γ` in `Kᶜ`, we enlarge `K` to a closed,
preconnected, unbounded subset `F ⊆ ℂ` of the plane, in a chart in which `γ` becomes a loop of the
plane avoiding `F`, and then apply `hplane`.

The chart is produced by a Möbius homeomorphism `Ψ` of the sphere which sends a suitable point `p`
of the complement of `K` to `∞`.  The point `p` is chosen in the *component* of the complement of
the range of `γ` that contains `K`, so that `K` can be joined to `p` by a path avoiding the loop;
`F` is the union of `Ψ '' K` and that path, cut off at the first time it reaches `∞`.

The auxiliary lemmas are:

* `mem_nhds_infty_ball` — the complements of closed balls are neighbourhoods of `∞`;
* `path_homotopic_of_homeomorph` — null-homotopies transport back along a homeomorphism;
* `closed_preconnected_unbounded_of_path_to_infty` — the enlarged set is a valid input for the
  plane crux;
* `exists_mem_componentIn_and_path` — the choice of the point moved to `∞` and of the path;
* `homotopic_refl_of_compl_eq_univ` — the degenerate case `K = ∅`.
-/

namespace Work.Smooth.JordanSeparation

open Set Filter
open scoped _root_.Topology

noncomputable section

/-! ## Auxiliary lemmas -/

/-- The complement of a closed ball is a neighbourhood of `∞` in `OnePoint ℂ`. -/
theorem mem_nhds_infty_ball {R : ℝ} :
    ((OnePoint.some '' {w : ℂ | R < ‖w‖}) ∪ {(OnePoint.infty : OnePoint ℂ)}) ∈
      𝓝 (OnePoint.infty) := by
  rw [OnePoint.nhds_infty_eq, Filter.mem_sup]
  refine ⟨?_, by simp⟩
  rw [Filter.mem_map]
  have hset : (OnePoint.some ⁻¹'
      ((OnePoint.some '' {w : ℂ | R < ‖w‖}) ∪ {(OnePoint.infty : OnePoint ℂ)}))
      = {w : ℂ | R < ‖w‖} := by
    ext w
    simp
  rw [hset]
  rw [Filter.coclosedCompact_eq_cocompact, Filter.mem_cocompact]
  refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, ?_⟩
  intro w hw
  rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero] at hw
  exact lt_of_not_ge hw

/-- A null-homotopy of loops transports back along a homeomorphism. -/
theorem path_homotopic_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {a : X} (γ : Path a a)
    (h : Path.Homotopic (γ.map e.continuous_toFun) (Path.refl (e a))) :
    Path.Homotopic γ (Path.refl a) := by
  obtain ⟨F⟩ := h
  refine ⟨{ toContinuousMap :=
              { toFun := fun p => e.symm (F p)
                continuous_toFun := e.symm.continuous.comp F.continuous }
            map_zero_left := fun t => ?_
            map_one_left := fun t => ?_
            prop' := fun t x hx => ?_ }⟩
  · show e.symm (F.toFun (0, t)) = γ t
    rw [F.map_zero_left]
    simpa using e.symm_apply_apply (γ t)
  · show e.symm (F.toFun (1, t)) = a
    rw [F.map_one_left]
    simpa using e.symm_apply_apply a
  · show e.symm (F.toFun (t, x)) = γ x
    have h2 : F.toFun (t, x) = e (γ x) := by simpa using F.prop' t x hx
    rw [h2]
    simpa using e.symm_apply_apply (γ x)

/-- If `u : unitInterval → OnePoint ℂ` is continuous and first hits `∞` at `t`, and `K` is a
compact preconnected subset of the sphere that avoids `∞` and contains `u 0`, then the finite part
of `K ∪ u '' [0, t)` is a closed, preconnected, unbounded subset of `ℂ`. -/
theorem closed_preconnected_unbounded_of_path_to_infty
    (K : Set (OnePoint ℂ)) (hKc : IsCompact K) (hKp : IsPreconnected K)
    (hinf : (OnePoint.infty : OnePoint ℂ) ∉ K)
    (u : unitInterval → OnePoint ℂ) (hu : Continuous u)
    (t : unitInterval) (ht : u t = OnePoint.infty)
    (htmin : ∀ s : unitInterval, u s = OnePoint.infty → t ≤ s)
    (hu0 : u 0 ≠ OnePoint.infty) (hK0 : u 0 ∈ K) :
    IsClosed {z : ℂ | (↑z : OnePoint ℂ) ∈ K ∪ u '' (Set.Iio t)} ∧
    IsPreconnected {z : ℂ | (↑z : OnePoint ℂ) ∈ K ∪ u '' (Set.Iio t)} ∧
    ∀ R : ℝ, ∃ z ∈ {z : ℂ | (↑z : OnePoint ℂ) ∈ K ∪ u '' (Set.Iio t)}, R ≤ ‖z‖ := by
  have ht0 : t ≠ 0 := fun h => hu0 (h ▸ ht)
  have htpos : (0 : unitInterval) < t :=
    lt_of_le_of_ne (zero_le : (0 : unitInterval) ≤ t) (Ne.symm ht0)
  have htpos' : (0 : ℝ) < (t : ℝ) := htpos
  set F : Set ℂ := {z : ℂ | (↑z : OnePoint ℂ) ∈ K ∪ u '' (Set.Iio t)} with hFdef
  -- `∞` is not in the set
  have hSinf : (OnePoint.infty : OnePoint ℂ) ∉ K ∪ u '' (Set.Iio t) := by
    rintro (h | ⟨s, hs, hs'⟩)
    · exact hinf h
    · exact absurd (htmin s hs') (not_le.mpr hs)
  -- preconnectedness
  have hSpre : IsPreconnected (K ∪ u '' (Set.Iio t)) := by
    have h1 : IsPreconnected (u '' (Set.Iio t)) :=
      (isPreconnected_Iio (a := t)).image u hu.continuousOn
    have h2 : (K ∩ u '' (Set.Iio t)).Nonempty := ⟨u 0, hK0, ⟨0, htpos, rfl⟩⟩
    exact IsPreconnected.union' h2 hKp h1
  have hFpre : IsPreconnected F :=
    hSpre.preimage_of_isOpenMap OnePoint.coe_injective OnePoint.isOpenMap_coe (fun y hy =>
      OnePoint.ne_infty_iff_exists.mp fun h => hSinf (h ▸ hy))
  -- closedness
  have hFc : IsClosed F := by
    have hclosed : IsClosed (K ∪ u '' (Set.Iic t)) := by
      refine hKc.isClosed.union ?_
      exact ((isClosed_Iic.isCompact.image hu)).isClosed
    have heq : F = OnePoint.some ⁻¹' (K ∪ u '' (Set.Iic t)) := by
      rw [hFdef]
      ext z
      constructor
      · rintro (h | ⟨s, hs, hs'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨s, Set.mem_Iic.mpr (le_of_lt (Set.mem_Iio.mp hs)), hs'⟩
      · rintro (h | ⟨s, hs, hs'⟩)
        · exact Or.inl h
        · rcases lt_or_eq_of_le (Set.mem_Iic.mp hs) with h' | h'
          · exact Or.inr ⟨s, h', hs'⟩
          · exact absurd (show (↑z : OnePoint ℂ) = OnePoint.infty from by rw [← hs', h', ht])
              (OnePoint.coe_ne_infty z)
    rw [heq]
    exact hclosed.preimage OnePoint.continuous_coe
  refine ⟨hFc, hFpre, ?_⟩
  -- unboundedness
  intro R
  have hW : ((OnePoint.some '' {w : ℂ | R < ‖w‖}) ∪ {(OnePoint.infty : OnePoint ℂ)}) ∈
      𝓝 (OnePoint.infty) := mem_nhds_infty_ball
  have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hquot : Tendsto (fun n : ℕ => (t : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have htn_mem : ∀ n : ℕ, (t : ℝ) - (t : ℝ) / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    have hle : (t : ℝ) / ((n : ℝ) + 1) ≤ (t : ℝ) := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith [t.2.1]
    have hnn : 0 ≤ (t : ℝ) / ((n : ℝ) + 1) := by positivity
    exact ⟨by linarith, by linarith [t.2.2]⟩
  let tn : ℕ → unitInterval := fun n => ⟨(t : ℝ) - (t : ℝ) / ((n : ℝ) + 1), htn_mem n⟩
  have htn_lt : ∀ n : ℕ, tn n < t := by
    intro n
    have hpos : 0 < (t : ℝ) / ((n : ℝ) + 1) :=
      div_pos htpos' (by positivity : (0 : ℝ) < (n : ℝ) + 1)
    show (t : ℝ) - (t : ℝ) / ((n : ℝ) + 1) < (t : ℝ)
    linarith
  have htn_tendsto : Tendsto tn atTop (𝓝 t) := by
    rw [tendsto_subtype_rng]
    have h2 : Tendsto (fun n : ℕ => (t : ℝ) - (t : ℝ) / ((n : ℝ) + 1)) atTop
        (𝓝 ((t : ℝ) - 0)) := tendsto_const_nhds.sub hquot
    simpa using h2
  have hseq : Tendsto (fun n : ℕ => u (tn n)) atTop (𝓝 (OnePoint.infty)) := by
    have h := hu.tendsto t
    rw [ht] at h
    exact h.comp htn_tendsto
  have hev : ∀ᶠ n : ℕ in atTop, u (tn n) ∈
      ((OnePoint.some '' {w : ℂ | R < ‖w‖}) ∪ {(OnePoint.infty : OnePoint ℂ)}) :=
    hseq.eventually hW
  obtain ⟨n, hn⟩ := hev.exists
  have hne : u (tn n) ≠ OnePoint.infty := fun h => absurd (htmin (tn n) h) (not_le.mpr (htn_lt n))
  rcases hn with ⟨z, hz, hz'⟩ | hinf'
  · refine ⟨z, ?_, le_of_lt hz⟩
    have hzU : ((↑z : OnePoint ℂ)) ∈ K ∪ u '' (Set.Iio t) := by
      rw [hz']
      exact Or.inr ⟨tn n, htn_lt n, rfl⟩
    exact hzU
  · exact absurd hinf' hne

/-- Given a compact preconnected `K` in the Riemann sphere that is not the whole sphere, a compact
`R` disjoint from `K`, and a point `k ∈ K`, there is a point `p` in the connected component of `k`
in `Rᶜ` with `p ∉ K`, and `k` can be joined to `p` by a path whose range lies in that component. -/
theorem exists_mem_componentIn_and_path {K R : Set (OnePoint ℂ)}
    (hKc : IsCompact K) (hKp : IsPreconnected K) (hKuniv : K ≠ Set.univ)
    (hRc : IsCompact R) (hRK : Disjoint R K) (k : OnePoint ℂ) (hk : k ∈ K) :
    ∃ p ∈ connectedComponentIn Rᶜ k, p ∉ K ∧
      ∃ A : Path k p, Set.range A ⊆ connectedComponentIn Rᶜ k := by
  haveI : LocallyPathConnectedSpace (OnePoint ℂ) := onePoint_locallyPathConnected
  have hKsub : K ⊆ Rᶜ := fun y hy hyR => Set.disjoint_left.mp hRK hyR hy
  have hKC : K ⊆ connectedComponentIn Rᶜ k := hKp.subset_connectedComponentIn hk hKsub
  have hCopen : IsOpen (connectedComponentIn Rᶜ k) := hRc.isClosed.isOpen_compl.connectedComponentIn
  have hCne : (connectedComponentIn Rᶜ k).Nonempty := ⟨k, mem_connectedComponentIn (hKsub hk)⟩
  have hCpre : IsPreconnected (connectedComponentIn Rᶜ k) := isPreconnected_connectedComponentIn
  have hCpath : IsPathConnected (connectedComponentIn Rᶜ k) :=
    (hCopen.isConnected_iff_isPathConnected).mp ⟨hCne, hCpre⟩
  have hnotsub : ¬ (connectedComponentIn Rᶜ k ⊆ K) := by
    intro hsub
    have heq : connectedComponentIn Rᶜ k = K := Subset.antisymm hsub hKC
    have hKopen : IsOpen K := heq ▸ hCopen
    have huniv : K = Set.univ := IsClopen.eq_univ ⟨hKc.isClosed, hKopen⟩ ⟨k, hk⟩
    exact hKuniv huniv
  obtain ⟨p, hpC, hpK⟩ := Set.not_subset.mp hnotsub
  refine ⟨p, hpC, hpK, ?_⟩
  obtain ⟨A, hA⟩ := hCpath.joinedIn k (mem_connectedComponentIn (hKsub hk)) p hpC
  exact ⟨A, fun y hy => by rcases hy with ⟨s, rfl⟩; exact hA s⟩

/-- Loops in `↥S` are null-homotopic when `S = univ` and the ambient space is simply connected. -/
theorem homotopic_refl_of_eq_univ {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
    {S : Set X} (hS : S = Set.univ) {a : X} (ha : a ∈ S)
    (γ : Path (⟨a, ha⟩ : ↥S) (⟨a, ha⟩ : ↥S)) : Path.Homotopic γ (Path.refl _) := by
  haveI : SimplyConnectedSpace X := ‹_›
  refine path_homotopic_of_homeomorph
    ((Homeomorph.setCongr hS).trans (Homeomorph.Set.univ X)) γ ?_
  exact (simply_connected_iff_loops_nullhomotopic.mp ‹SimplyConnectedSpace X›).2 _ _

/-! ## The main theorem -/

theorem sphere_reduction_of_plane_crux
    (hplane : ∀ (F : Set ℂ), IsClosed F → IsPreconnected F → (∀ R : ℝ, ∃ z ∈ F, R ≤ ‖z‖) →
      ∀ {x : ℂ} (hx : x ∉ F), ∀ γ : Path (⟨x, hx⟩ : ↥Fᶜ) (⟨x, hx⟩ : ↥Fᶜ),
        Path.Homotopic γ (Path.refl _))
    (hsphere : SimplyConnectedSpace (OnePoint ℂ))
    (K : Set (OnePoint ℂ)) (hKc : IsCompact K) (hKp : IsPreconnected K) {x : OnePoint ℂ}
    (hx : x ∉ K) (γ : Path (⟨x, hx⟩ : ↥(Kᶜ)) (⟨x, hx⟩ : ↥(Kᶜ))) :
    Path.Homotopic γ (Path.refl _) := by
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · -- `K = ∅`: the sphere is simply connected
    exact homotopic_refl_of_eq_univ (S := Kᶜ) (by rw [hK0, Set.compl_empty]) hx γ
  · -- `K ≠ ∅`
    obtain ⟨k, hk⟩ := hKne
    have hγcont : Continuous (fun t : unitInterval => ((γ t : ↥(Kᶜ)) : OnePoint ℂ)) :=
      continuous_subtype_val.comp γ.continuous
    set R : Set (OnePoint ℂ) :=
      Set.range (fun t : unitInterval => ((γ t : ↥(Kᶜ)) : OnePoint ℂ)) with hRdef
    have hγmem : ∀ t : unitInterval, ((γ t : ↥(Kᶜ)) : OnePoint ℂ) ∈ R := fun t =>
      Set.mem_range_self t
    have hRc : IsCompact R := isCompact_range hγcont
    have hRK : Disjoint R K := by
      rw [Set.disjoint_left]
      rintro y ⟨t, rfl⟩ hy
      exact (γ t).2 hy
    have hKuniv : K ≠ Set.univ := fun h => hx (h ▸ Set.mem_univ x)
    obtain ⟨p, hpC, hpK, A, hA⟩ :=
      exists_mem_componentIn_and_path hKc hKp hKuniv hRc hRK k hk
    have hpR : p ∉ R := connectedComponentIn_subset Rᶜ k hpC
    have hγK : ∀ s : unitInterval, ((γ s : ↥(Kᶜ)) : OnePoint ℂ) ∉ K := fun s => (γ s).2
    have hAR : Set.range A ⊆ Rᶜ := fun y hy => connectedComponentIn_subset Rᶜ k (hA hy)
    -- the Möbius homeomorphism moving `p` to `∞`
    obtain ⟨Ψ, hΨp⟩ : ∃ Ψ : OnePoint ℂ ≃ₜ OnePoint ℂ, Ψ p = OnePoint.infty := by
      by_cases hp : p = OnePoint.infty
      · exact ⟨Homeomorph.refl _, hp⟩
      · obtain ⟨p₀, hp₀⟩ := OnePoint.ne_infty_iff_exists.mp hp
        obtain ⟨Φ, hMobInf, hΦ0, hΦz⟩ := Work.Smooth.SphereJordan.mobiusAddInv p₀
        exact ⟨Φ.symm, by rw [← hp₀, ← hMobInf, Homeomorph.symm_apply_apply]⟩
    have hΨeq : ∀ {y : OnePoint ℂ}, Ψ y = OnePoint.infty ↔ y = p := fun {y} =>
      ⟨fun h => Ψ.injective (h.trans hΨp.symm), fun h => by rw [h, hΨp]⟩
    set K' : Set (OnePoint ℂ) := Ψ '' K with hK'def
    have hK'c : IsCompact K' := hKc.image Ψ.continuous
    have hK'p : IsPreconnected K' := hKp.image _ Ψ.continuous.continuousOn
    have hinfK' : (OnePoint.infty : OnePoint ℂ) ∉ K' := by
      rintro ⟨y, hy, hy'⟩
      exact hpK ((hΨeq.mp hy') ▸ hy)
    have hu : Continuous (fun s : unitInterval => Ψ (A s)) := Ψ.continuous.comp A.continuous
    have hu0 : Ψ (A 0) ≠ OnePoint.infty := by
      rw [A.source]
      intro h
      exact hpK ((hΨeq.mp h) ▸ hk)
    have huK : Ψ (A 0) ∈ K' := ⟨k, hk, congrArg Ψ A.source.symm⟩
    -- the first hitting time of `∞`
    set T : Set unitInterval := (fun s : unitInterval => Ψ (A s)) ⁻¹' {OnePoint.infty} with hTdef
    have hTne : T.Nonempty :=
      ⟨1, by show Ψ (A 1) = OnePoint.infty; rw [A.target]; exact hΨp⟩
    have hTclosed : IsClosed T := isClosed_singleton.preimage hu
    have hTbdd : BddBelow T := ⟨0, fun s _ => s.2.1⟩
    have hTmem : sInf T ∈ T := hTclosed.csInf_mem hTne hTbdd
    set t : unitInterval := sInf T with htdef
    have ht : Ψ (A t) = OnePoint.infty := hTmem
    have htmin : ∀ s : unitInterval, Ψ (A s) = OnePoint.infty → t ≤ s :=
      fun s hs => csInf_le hTbdd hs
    obtain ⟨hFc, hFpre, hFunb⟩ := closed_preconnected_unbounded_of_path_to_infty K' hK'c hK'p
      hinfK' (fun s : unitInterval => Ψ (A s)) hu t ht htmin hu0 huK
    set F : Set ℂ := {z : ℂ | (↑z : OnePoint ℂ) ∈
      K' ∪ (fun s : unitInterval => Ψ (A s)) '' (Set.Iio t)} with hFdef
    have hUF : ∀ z : ℂ, (↑z : OnePoint ℂ) ∈ K' →
        z ∈ ({z : ℂ | (↑z : OnePoint ℂ) ∈ K' ∪ (fun s : unitInterval => Ψ (A s)) '' (Set.Iio t)}) :=
      fun z hz => Or.inl hz
    have hFc' : IsClosed F := by rw [hFdef]; exact hFc
    have hFpre' : IsPreconnected F := by rw [hFdef]; exact hFpre
    have hFunb' : ∀ R : ℝ, ∃ z ∈ F, R ≤ ‖z‖ := by rw [hFdef]; exact hFunb
    -- the points of the loop in the sphere picture avoid `K' ∪ u '' Iio t`
    have hnotS : ∀ s : unitInterval,
        Ψ ((γ s : ↥(Kᶜ)) : OnePoint ℂ) ∉ K' ∪ (fun r : unitInterval => Ψ (A r)) '' (Set.Iio t) := by
      intro s
      rintro (h | ⟨r, hr, hr'⟩)
      · obtain ⟨y, hy, hy'⟩ := h
        have hy'' : y = ((γ s : ↥(Kᶜ)) : OnePoint ℂ) := Ψ.injective hy'
        exact hγK s (hy'' ▸ hy)
      · have hEq : A r = (γ s : OnePoint ℂ) := Ψ.injective hr'
        exact hAR (Set.mem_range_self r) (hEq ▸ hγmem s)
    have hneS : ∀ s : unitInterval, Ψ ((γ s : ↥(Kᶜ)) : OnePoint ℂ) ≠ OnePoint.infty := by
      intro s h
      have hEq : ((γ s : ↥(Kᶜ)) : OnePoint ℂ) = p := hΨeq.mp h
      exact hpR (hEq ▸ hγmem s)
    have hmemF : ∀ s : unitInterval,
        Ψ ((γ s : ↥(Kᶜ)) : OnePoint ℂ) ∈ OnePoint.some '' Fᶜ := by
      intro s
      obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp (hneS s)
      refine ⟨z, ?_, hz⟩
      intro hzF
      exact hnotS s (by rw [← hz]; exact hzF)
    -- the loop in `↥(some '' Fᶜ)`
    have hxval : ((γ 0 : ↥(Kᶜ)) : OnePoint ℂ) = x := congrArg Subtype.val γ.source
    have hmemc : Ψ x ∈ OnePoint.some '' Fᶜ := by
      rw [← hxval]
      exact hmemF 0
    set c : ↥(OnePoint.some '' Fᶜ) := ⟨Ψ x, hmemc⟩ with hcdef
    have hcval : (c : OnePoint ℂ) = Ψ x := rfl
    have hγScont : Continuous (fun s : unitInterval =>
        (⟨Ψ ((γ s : ↥(Kᶜ)) : OnePoint ℂ), hmemF s⟩ : ↥(OnePoint.some '' Fᶜ))) :=
      Continuous.subtype_mk (Ψ.continuous.comp hγcont) hmemF
    let γS : Path c c :=
      { toFun := fun s => ⟨Ψ ((γ s : ↥(Kᶜ)) : OnePoint ℂ), hmemF s⟩
        continuous_toFun := hγScont
        source' := Subtype.ext (by
          show Ψ ((γ 0 : ↥(Kᶜ)) : OnePoint ℂ) = Ψ x
          rw [hxval])
        target' := Subtype.ext (by
          show Ψ ((γ 1 : ↥(Kᶜ)) : OnePoint ℂ) = Ψ x
          rw [show ((γ 1 : ↥(Kᶜ)) : OnePoint ℂ) = x from congrArg Subtype.val γ.target]) }
    -- the homeomorphism `↥(Fᶜ) ≃ₜ ↥(some '' Fᶜ)`
    let eF : ↥(Fᶜ) ≃ₜ ↥(OnePoint.some '' Fᶜ) :=
      (OnePoint.isOpenEmbedding_coe (X := ℂ)).toIsEmbedding.homeomorphImage Fᶜ
    let γF : Path (eF.symm c) (eF.symm c) := γS.map eF.symm.continuous_toFun
    obtain ⟨F0⟩ := hplane F hFc' hFpre' hFunb' (x := (eF.symm c).1) (eF.symm c).2 γF
    -- the resulting null-homotopy of `γ`, built explicitly
    have hval : Continuous (fun q : unitInterval × unitInterval =>
        Ψ.symm (((F0 q).1 : ℂ) : OnePoint ℂ)) :=
      Ψ.symm.continuous.comp (OnePoint.continuous_coe.comp (continuous_subtype_val.comp F0.continuous))
    have hmemK : ∀ q : unitInterval × unitInterval,
        Ψ.symm (((F0 q).1 : ℂ) : OnePoint ℂ) ∈ Kᶜ := by
      rintro ⟨s, r⟩ hK
      have hK'' : (((F0 (s, r)).1 : ℂ) : OnePoint ℂ) ∈ K' :=
        ⟨Ψ.symm (((F0 (s, r)).1 : ℂ) : OnePoint ℂ), hK, by rw [Homeomorph.apply_symm_apply]⟩
      exact (F0 (s, r)).2 (hUF _ hK'')
    have hγFval : ∀ s : unitInterval,
        ((↑((γF s : ↥(Fᶜ)).1) : OnePoint ℂ)) = (γS s : OnePoint ℂ) := by
      intro s
      have h3 : (γF s : ↥(Fᶜ)) = eF.symm (γS s) := rfl
      rw [h3]
      have h2 : (eF (eF.symm (γS s)) : OnePoint ℂ) = (γS s : OnePoint ℂ) := by
        rw [Homeomorph.apply_symm_apply]
      exact h2
    have hγSval : ∀ s : unitInterval, (γS s : OnePoint ℂ) = Ψ ((γ s : ↥(Kᶜ)) : OnePoint ℂ) :=
      fun s => rfl
    have hF0zero : ∀ s : unitInterval, (F0 (0, s)).1 = (γF s).1 := fun s =>
      congrArg Subtype.val (F0.map_zero_left s)
    have hF0one : ∀ s : unitInterval, (F0 (1, s)).1 = (eF.symm c).1 := fun s =>
      congrArg Subtype.val (F0.map_one_left s)
    have hF0prop0 : ∀ s : unitInterval, (F0 (s, 0)).1 = (γF 0).1 := fun s =>
      congrArg Subtype.val (F0.prop' s 0 (Or.inl rfl))
    have hF0prop1 : ∀ s : unitInterval, (F0 (s, 1)).1 = (γF 1).1 := fun s =>
      congrArg Subtype.val (F0.prop' s 1 (Or.inr rfl))
    let Φ : unitInterval × unitInterval → ↥(Kᶜ) :=
      fun q => ⟨Ψ.symm (((F0 q).1 : ℂ) : OnePoint ℂ), hmemK q⟩
    have hΦcont : Continuous Φ := Continuous.subtype_mk hval hmemK
    have hmzl : ∀ s : unitInterval, Φ (0, s) = γ s := by
      intro s
      apply Subtype.ext
      show Ψ.symm (((F0 (0, s)).1 : ℂ) : OnePoint ℂ) = ((γ s : ↥(Kᶜ)) : OnePoint ℂ)
      rw [hF0zero s, hγFval s, hγSval s, Homeomorph.symm_apply_apply]
    have hcEval : ((↑((eF.symm c : ↥(Fᶜ)).1) : OnePoint ℂ)) = Ψ x := by
      have h2 : (eF (eF.symm c) : OnePoint ℂ) = (c : OnePoint ℂ) := by
        rw [Homeomorph.apply_symm_apply]
      have h3 : (c : OnePoint ℂ) = Ψ x := rfl
      rw [h3] at h2
      exact h2
    have hmol : ∀ s : unitInterval, Φ (1, s) = ⟨x, hx⟩ := by
      intro s
      apply Subtype.ext
      show Ψ.symm (((F0 (1, s)).1 : ℂ) : OnePoint ℂ) = x
      rw [hF0one s, hcEval, Homeomorph.symm_apply_apply]
    have hprop : ∀ s z : unitInterval, z ∈ ({0, 1} : Set unitInterval) → Φ (s, z) = γ z := by
      intro s z hz
      rcases hz with hz | hz
      · subst hz
        apply Subtype.ext
        show Ψ.symm (((F0 (s, 0)).1 : ℂ) : OnePoint ℂ) = ((γ 0 : ↥(Kᶜ)) : OnePoint ℂ)
        rw [hF0prop0 s, hγFval 0, hγSval 0, Homeomorph.symm_apply_apply]
      · subst hz
        apply Subtype.ext
        show Ψ.symm (((F0 (s, 1)).1 : ℂ) : OnePoint ℂ) = ((γ 1 : ↥(Kᶜ)) : OnePoint ℂ)
        rw [hF0prop1 s, hγFval 1, hγSval 1, Homeomorph.symm_apply_apply]
    exact ⟨{ toFun := Φ
             continuous_toFun := hΦcont
             map_zero_left := hmzl
             map_one_left := hmol
             prop' := hprop }⟩

end

end Work.Smooth.JordanSeparation

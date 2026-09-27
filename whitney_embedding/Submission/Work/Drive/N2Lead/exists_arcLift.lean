import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2C.exists_localPhase_of_immersed_curve
import Submission.Work.Compat.MFDerivCongrV433

/-!
# Lifting a curve inside one component of a level to the parameter of the component

`Work.Drive.N2Lead.exists_arcLift`: if `α` is a smooth immersion of the line whose image on an open
preconnected `J ⊆ ℝ` lies in the range of one component curve `L.γ i` of a `LevelCurves`
parametrisation of the level `f = b`, then `α` is `L.γ i` composed with a `C^∞` parameter change `τ`
of nonvanishing derivative, and `τ` is monotone (increasing or decreasing).

The route (all steps proved below):

* `mfderiv_γ_ne_zero` — the `ker` row of `LevelCurves` forces each component curve to be an
  immersion (a tangent space of the surface is `2`-dimensional, the level direction is
  `1`-dimensional);
* `exists_local_rightInverse` — from a local phase `φ` of `γ` near `t₀` (`φ (γ t) = t` for `t` near
  `t₀`) one gets `γ (φ y) = y` for all `y` near `γ t₀` in the range of `γ`, using only continuity,
  the period and the fact that the fibres of `γ` are cosets of `ℤ`;
* `exists_local_piece_of` — a local piece of the lift (`φ ∘ α`), an ord-connected relatively open
  interval of `J`;
* `AnchoredPiece`, `anchoredPiece_uniq`, `anchoredPiece_exists`, `exists_continuous_lift` — the
  local pieces glue to a global continuous lift on the interval `J` anchored at one point (the
  anchored pieces form a set which is both open and closed in `J`; two of them agree because the
  difference of two lifts is a continuous `ℤ`-valued function on an ord-connected set);
* `contDiffOn_of_lift`, `deriv_ne_zero_of_lift`, `strictMonoOn_or_strictAntiOn_of_deriv_ne_zero` —
  smoothness of the lift from the local phase, nonvanishing of `τ'` from the chain rule (using
  `α` being an immersion), and monotonicity from the intermediate value theorem.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

local notation "Cinf" => ((⊤ : ℕ∞) : WithTop ℕ∞)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) Cinf M] [T2Space M]

/-- Integer periods. -/
lemma per_int {γ : ℝ → M} (hper : ∀ x : ℝ, γ (x + 1) = γ x) (x : ℝ) (k : ℤ) :
    γ (x + k) = γ x := by
  have hp : Function.Periodic γ (1 : ℝ) := hper
  simpa using (hp.zsmul k) x

/-- The component curve of a `LevelCurves` datum is an immersion: the `ker` row forces its
differential to be nonzero (the tangent space of the surface is `2`-dimensional, the target of
`mfderiv f` is `1`-dimensional). -/
lemma mfderiv_γ_ne_zero {f : M → ℝ} {b : ℝ} {n : ℕ} (L : Work.Drive.N2C.LevelCurves f b n)
    (i : Fin n) (x : ℝ) : mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) x 1 ≠ 0 := by
  intro h0
  have hzero : mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) x = 0 := by
    let g : ℝ →L[ℝ] TangentSpace (𝓡 2) (L.γ i x) := mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) x
    change g = 0
    exact ContinuousLinearMap.ext_ring (by rw [zero_apply]; exact h0)
  have hker : (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (L.γ i x)).ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨t, ht⟩ := L.ker i x v hv
    rw [← ht, hzero]
    rfl
  have hinj : Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (L.γ i x)) :=
    LinearMap.ker_eq_bot.mp hker
  haveI : Module.Finite ℝ (TangentSpace 𝓘(ℝ,ℝ) (f (L.γ i x))) :=
    inferInstanceAs (Module.Finite ℝ ℝ)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have h1 : Module.finrank ℝ (TangentSpace (𝓡 2) (L.γ i x)) = 2 := finrank_euclideanSpace
  have h2 : Module.finrank ℝ (TangentSpace 𝓘(ℝ,ℝ) (f (L.γ i x))) = 1 := Module.finrank_self ℝ
  omega

/-- A continuous integer-valued function on a preconnected set of `ℝ` is constant. -/
lemma eq_of_preconnected_of_int {T : Set ℝ} (hT : IsPreconnected T)
    (hint : ∀ t ∈ T, ∃ k : ℤ, t = k) {x y : ℝ} (hx : x ∈ T) (hy : y ∈ T) : x = y := by
  by_contra hxy
  have hord : T.OrdConnected := hT.ordConnected
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · obtain ⟨kx, rfl⟩ := hint x hx
    obtain ⟨ky, rfl⟩ := hint y hy
    have hkxky : kx < ky := by exact_mod_cast hlt
    have hmid : ((kx : ℝ) + 1 / 2) ∈ T := by
      refine hord.out hx hy ⟨by linarith, ?_⟩
      have hle : (kx:ℝ) + 1 ≤ (ky:ℝ) := by
        have : kx + 1 ≤ ky := by omega
        exact_mod_cast this
      linarith
    obtain ⟨m, hm⟩ := hint _ hmid
    have h2 : (2 * (m - kx) : ℤ) = 1 := by
      have : ((2 * (m - kx) : ℤ) : ℝ) = (1 : ℝ) := by
        push_cast
        linarith [hm]
      exact_mod_cast this
    omega
  · -- symmetric
    obtain ⟨ky, hky⟩ := hint y hy
    obtain ⟨kx, hkx⟩ := hint x hx
    have hkykx : ky < kx := by
      have : (ky : ℝ) < (kx : ℝ) := by linarith [hky, hkx, hgt]
      exact_mod_cast this
    have hmid : ((ky : ℝ) + 1 / 2) ∈ T := by
      refine hord.out hy hx ⟨by linarith, ?_⟩
      have hle : (ky:ℝ) + 1 ≤ (kx:ℝ) := by
        have : ky + 1 ≤ kx := by omega
        exact_mod_cast this
      linarith
    obtain ⟨m, hm⟩ := hint _ hmid
    have h2 : (2 * (m - ky) : ℤ) = 1 := by
      have : ((2 * (m - ky) : ℤ) : ℝ) = (1 : ℝ) := by
        push_cast
        linarith [hm]
      exact_mod_cast this
    omega

/-- A continuous integer-valued function on a preconnected set is constant. -/
lemma eq_of_continuousOn_int_valued {S : Set ℝ} (hS : IsPreconnected S) {h : ℝ → ℝ}
    (hh : ContinuousOn h S) (hint : ∀ x ∈ S, ∃ k : ℤ, h x = k) {x y : ℝ} (hx : x ∈ S)
    (hy : y ∈ S) : h x = h y :=
  eq_of_preconnected_of_int (hS.image h hh) (by rintro t ⟨z, hz, rfl⟩; exact hint z hz)
    ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

/-- The union of two ord-connected subsets of `ℝ` meeting in a point is ord-connected. -/
lemma ordConnected_union_of_mem {A B : Set ℝ} (hA : A.OrdConnected) (hB : B.OrdConnected)
    {u : ℝ} (huA : u ∈ A) (huB : u ∈ B) : (A ∪ B).OrdConnected := by
  refine Set.OrdConnected.mk (fun x hx y hy z hz => ?_)
  rcases hz with ⟨hz1, hz2⟩
  by_cases hzu : z ≤ u
  · rcases hx with hxA | hxB
    · exact Or.inl (hA.out hxA huA ⟨hz1, hzu⟩)
    · exact Or.inr (hB.out hxB huB ⟨hz1, hzu⟩)
  · have huz : u ≤ z := le_of_lt (not_le.mp hzu)
    rcases hy with hyA | hyB
    · exact Or.inl (hA.out huA hyA ⟨huz, hz2⟩)
    · exact Or.inr (hB.out huB hyB ⟨huz, hz2⟩)


/-- **Local right inverse of a periodic curve.**  If `φ` inverts `γ` on the parameters near `t₀`,
then `γ (φ y) = y` for all `y` near `γ t₀` that lie in the range of `γ`. -/
lemma exists_local_rightInverse {γ : ℝ → M} (hγc : Continuous γ)
    (hper : ∀ x : ℝ, γ (x + 1) = γ x)
    (hmod : ∀ x y : ℝ, γ x = γ y → ∃ k : ℤ, x = y + k)
    (t₀ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {φ : M → ℝ} (hφ : ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), φ (γ t) = t) :
    ∃ W : Set M, IsOpen W ∧ γ t₀ ∈ W ∧ ∀ y ∈ W, y ∈ Set.range γ → γ (φ y) = y := by
  have hδ' : (0 : ℝ) < min δ (1 / 2) := lt_min hδ (by norm_num)
  have hbad1 : ∀ a ∈ Icc (t₀ + min δ (1 / 2)) (t₀ + 1 / 2), γ a ≠ γ t₀ := by
    intro s hs hse
    obtain ⟨k, hk⟩ := hmod s t₀ hse
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      have : (0 : ℝ) < s - t₀ := by linarith [hs.1, hδ']
      linarith
    have hklt : (k : ℝ) < 1 := by
      have : s - t₀ < 1 := by linarith [hs.2]
      linarith
    have h1 : (0 : ℤ) < k := by exact_mod_cast hkpos
    have h2 : k < 1 := by exact_mod_cast hklt
    omega
  have hbad2 : ∀ a ∈ Icc (t₀ - 1 / 2) (t₀ - min δ (1 / 2)), γ a ≠ γ t₀ := by
    intro s hs hse
    obtain ⟨k, hk⟩ := hmod s t₀ hse
    have hkpos : (k : ℝ) < 0 := by
      have : s - t₀ ≤ -min δ (1 / 2) := by linarith [hs.2]
      linarith
    have hklt : (-1 : ℝ) < (k : ℝ) := by
      have : (-1 : ℝ) < s - t₀ := by linarith [hs.1]
      linarith
    have h1 : k < 0 := by exact_mod_cast hkpos
    have h2 : (-1 : ℤ) < k := by exact_mod_cast hklt
    omega
  obtain ⟨W, hWopen, ht₀W, hW⟩ :
      ∃ W : Set M, IsOpen W ∧ γ t₀ ∈ W ∧
        ∀ y ∈ W, y ∉ γ '' (Icc (t₀ + min δ (1 / 2)) (t₀ + 1 / 2) ∪
          Icc (t₀ - 1 / 2) (t₀ - min δ (1 / 2))) := by
    refine ⟨_ᶜ, ?_, ?_, fun y hy => hy⟩
    · exact ((isCompact_Icc.union isCompact_Icc).image hγc).isClosed.isOpen_compl
    · rintro ⟨a, ha, heq⟩
      rcases ha with ha | ha
      · exact hbad1 a ha heq
      · exact hbad2 a ha heq
  refine ⟨W, hWopen, ht₀W, ?_⟩
  intro y hyW hyrange
  obtain ⟨s, rfl⟩ := hyrange
  have hrepr : ∃ s' : ℝ, γ s' = γ s ∧ s' ∈ Ico (t₀ - 1 / 2) (t₀ + 1 / 2) := by
    refine ⟨t₀ + (Int.fract (s - t₀ + 1 / 2) - 1 / 2), ?_, ?_⟩
    · have hk : t₀ + (Int.fract (s - t₀ + 1 / 2) - 1 / 2)
          = s + (-(Int.floor (s - t₀ + 1 / 2)) : ℤ) := by
        have := Int.fract_add_floor (s - t₀ + 1 / 2)
        push_cast
        linarith
      rw [hk, per_int hper]
    · have h1 := Int.fract_nonneg (s - t₀ + 1 / 2)
      have h2 := Int.fract_lt_one (s - t₀ + 1 / 2)
      exact ⟨by linarith, by linarith⟩
  obtain ⟨s', hs'γ, hs'mem⟩ := hrepr
  have hnotbad : γ s ∉ γ '' (Icc (t₀ + min δ (1 / 2)) (t₀ + 1 / 2) ∪
      Icc (t₀ - 1 / 2) (t₀ - min δ (1 / 2))) := hW (γ s) hyW
  have hnot1 : ¬ (t₀ + min δ (1 / 2) ≤ s') := by
    intro hge
    exact hnotbad ⟨s', Or.inl ⟨hge, le_of_lt hs'mem.2⟩, hs'γ⟩
  have hnot2 : ¬ (s' ≤ t₀ - min δ (1 / 2)) := by
    intro hle
    exact hnotbad ⟨s', Or.inr ⟨hs'mem.1, hle⟩, hs'γ⟩
  have hs'δ : s' ∈ Ioo (t₀ - δ) (t₀ + δ) :=
    ⟨by linarith [not_le.mp hnot2, min_le_left δ (1 / 2)],
     by linarith [not_le.mp hnot1, min_le_left δ (1 / 2)]⟩
  rw [← hs'γ, hφ s' hs'δ, hs'γ]

/-- **A local piece of the lift.**  Given a parameter `t` of the component curve over `α w`, there is
a relatively open interval piece `V ∋ w` of `J` on which `α` is lifted by the smooth expression
`φ ∘ α`, anchored at `t`. -/
lemma exists_local_piece_of {f : M → ℝ} {b : ℝ} {n : ℕ} (L : Work.Drive.N2C.LevelCurves f b n)
    (i : Fin n) {α : ℝ → M} (hα : ContMDiff 𝓘(ℝ,ℝ) (𝓡 2) Cinf α)
    (himm : ∀ t : ℝ, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) t 1 ≠ 0)
    {J : Set ℝ} (hJ : IsOpen J) (hJc : IsPreconnected J)
    (hJα : ∀ w ∈ J, α w ∈ Set.range (L.γ i)) (w : ℝ) (hw : w ∈ J) (t : ℝ)
    (ht : L.γ i t = α w) :
    ∃ (V : Set ℝ) (τ_V : ℝ → ℝ), V ⊆ J ∧ IsOpen V ∧ V.OrdConnected ∧ w ∈ V ∧
      ContinuousOn τ_V V ∧ (∀ u ∈ V, L.γ i (τ_V u) = α u) ∧ τ_V w = t := by
  obtain ⟨U, φ, hUopen, htU, hφsm, δ, hδpos, hφ⟩ :=
    Work.Drive.N2C.exists_localPhase_of_immersed_curve (L.γ i) (L.sm i) himm t
  obtain ⟨W, hWopen, htW, hW⟩ :=
    exists_local_rightInverse (L.sm i).continuous (L.per i) (L.modOne i) t hδpos hφ
  have hWUopen : IsOpen (W ∩ U) := hWopen.inter hUopen
  have htWU : L.γ i t ∈ W ∩ U := ⟨htW, htU⟩
  have hV₀open : IsOpen (α ⁻¹' (W ∩ U) ∩ J) := (hWUopen.preimage hα.continuous).inter hJ
  have hwV₀ : w ∈ α ⁻¹' (W ∩ U) ∩ J := ⟨by change α w ∈ W ∩ U; rw [← ht]; exact htWU, hw⟩
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hV₀open w hwV₀
  refine ⟨J ∩ Ioo (w - ε) (w + ε), fun u => φ (α u), inter_subset_left, hJ.inter isOpen_Ioo,
    ?_, ⟨hw, by rw [mem_Ioo]; exact ⟨by linarith, by linarith⟩⟩, ?_, ?_, ?_⟩
  · exact (convex_iff_ordConnected.mpr hJc.ordConnected).ordConnected.inter
      (convex_Ioo _ _).ordConnected
  · refine ContinuousOn.comp (t := W ∩ U) (hφsm.continuousOn.mono inter_subset_right)
      hα.continuous.continuousOn (fun u hu => ?_)
    have hu' : u ∈ Metric.ball w ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [(mem_Ioo.mp hu.2).1], by linarith [(mem_Ioo.mp hu.2).2]⟩
    exact Set.mem_preimage.mp (hεsub hu').1
  · intro u hu
    have hu' : u ∈ Metric.ball w ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [(mem_Ioo.mp hu.2).1], by linarith [(mem_Ioo.mp hu.2).2]⟩
    have huW : α u ∈ W := (Set.mem_preimage.mp (hεsub hu').1).1
    exact hW (α u) huW (hJα u hu.1)
  · change φ (α w) = t
    rw [← ht]
    exact hφ t ⟨by linarith [hδpos], by linarith [hδpos]⟩

/-- An *anchored piece*: an interval piece of `J` containing `w₀` and `w`, on which `γ` admits a
continuous lift of `α` taking the value `t₀` at `w₀` and `v` at `w`. -/
def AnchoredPiece (γ α : ℝ → M) (J : Set ℝ) (w₀ t₀ : ℝ) (w v : ℝ) : Prop :=
  ∃ (V : Set ℝ) (τ_V : ℝ → ℝ), V ⊆ J ∧ IsOpen V ∧ V.OrdConnected ∧ w₀ ∈ V ∧ w ∈ V ∧
    ContinuousOn τ_V V ∧ (∀ u ∈ V, γ (τ_V u) = α u) ∧ τ_V w₀ = t₀ ∧ τ_V w = v

/-- Anchored pieces are unique. -/
lemma anchoredPiece_uniq {γ α : ℝ → M} {J : Set ℝ} {w₀ t₀ w v v' : ℝ}
    (hmod : ∀ x y : ℝ, γ x = γ y → ∃ k : ℤ, x = y + k)
    (h : AnchoredPiece γ α J w₀ t₀ w v) (h' : AnchoredPiece γ α J w₀ t₀ w v') : v = v' := by
  obtain ⟨V, τV, hVJ, hVopen, hVord, hw₀V, hwV, hVcont, hVlift, hVanch, hVw⟩ := h
  obtain ⟨V', τ', hV'J, hV'open, hV'ord, hw₀V', hwV', hV'cont, hV'lift, hV'anch, hV'w⟩ := h'
  have hcont : ContinuousOn (fun x => τV x - τ' x) (V ∩ V') :=
    (hVcont.mono inter_subset_left).sub (hV'cont.mono inter_subset_right)
  have hint : ∀ x ∈ V ∩ V', ∃ k : ℤ, τV x - τ' x = k := by
    intro x hx
    obtain ⟨k, hk⟩ := hmod (τV x) (τ' x) (by rw [hVlift x hx.1, hV'lift x hx.2])
    exact ⟨k, by rw [hk]; push_cast; ring⟩
  have hconst := eq_of_continuousOn_int_valued ((hVord.inter hV'ord).isPreconnected) hcont hint
    ⟨hw₀V, hw₀V'⟩ ⟨hwV, hwV'⟩
  rw [hVanch, hV'anch, sub_self] at hconst
  rw [hVw, hV'w] at hconst
  linarith

/-- **Existence of anchored pieces.**  Along the preconnected `J` every point is reached by an
anchored piece: the set of points reached by an anchored piece is open (one can extend along the
piece) and closed in `J` (`w ∈ closure S` gives a point `u` of the local piece at `w` that is
already reached; gluing the two pieces along the integer-valued difference of their lifts produces
an anchored piece through `w`). -/
lemma anchoredPiece_exists {γ α : ℝ → M} {J : Set ℝ} (hJ : IsOpen J)
    (hJc : IsPreconnected J) (hJα : ∀ w ∈ J, α w ∈ Set.range γ)
    (hmod : ∀ x y : ℝ, γ x = γ y → ∃ k : ℤ, x = y + k)
    (hper : ∀ x : ℝ, γ (x + 1) = γ x)
    (hpiece : ∀ (w : ℝ) (hw : w ∈ J) (t : ℝ), γ t = α w →
       ∃ (V : Set ℝ) (τ_V : ℝ → ℝ), V ⊆ J ∧ IsOpen V ∧ V.OrdConnected ∧ w ∈ V ∧
         ContinuousOn τ_V V ∧ (∀ u ∈ V, γ (τ_V u) = α u) ∧ τ_V w = t)
    {w₀ : ℝ} (hw₀ : w₀ ∈ J) {t₀ : ℝ} (ht₀ : γ t₀ = α w₀) :
    ∀ w ∈ J, ∃ v, AnchoredPiece γ α J w₀ t₀ w v := by
  classical
  let S : Set ℝ := {w | w ∈ J ∧ ∃ v, AnchoredPiece γ α J w₀ t₀ w v}
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨hwJ, v, V, τV, hVJ, hVopen, hVord, hw₀V, hwV, hVcont, hVlift, hVanch, hVw⟩
    refine Filter.mem_of_superset (hVopen.mem_nhds hwV) ?_
    intro u hu
    exact ⟨hVJ hu, ⟨τV u, V, τV, hVJ, hVopen, hVord, hw₀V, hu, hVcont, hVlift, hVanch, rfl⟩⟩
  have hw₀S : w₀ ∈ S := by
    obtain ⟨V, τV, hVJ, hVopen, hVord, hw₀V, hVcont, hVlift, hVanch⟩ := hpiece w₀ hw₀ t₀ ht₀
    exact ⟨hw₀, ⟨t₀, V, τV, hVJ, hVopen, hVord, hw₀V, hw₀V, hVcont, hVlift, hVanch, hVanch⟩⟩
  have hkey : ∀ w ∈ J, w ∈ closure S → w ∈ S := by
    intro w hwJ hwcl
    obtain ⟨tw, htw⟩ := hJα w hwJ
    obtain ⟨Vw, τw, hVwJ, hVwopen, hVword, hwVw, hVwcont, hVwlift, hVww⟩ :=
      hpiece w hwJ tw htw
    obtain ⟨u, huVw, huS⟩ := (mem_closure_iff_nhds.mp hwcl) Vw (hVwopen.mem_nhds hwVw)
    obtain ⟨huJ, v, Vu, τu, hVuJ, hVuopen, hVuord, hw₀Vu, huVu, hVucont, hVulift, hVuanch,
      hVuv⟩ := huS
    obtain ⟨k, hk⟩ := hmod (τu u) (τw u) (by rw [hVulift u huVu, hVwlift u huVw])
    have hdiff : ∀ x ∈ Vu ∩ Vw, τu x - τw x = τu u - τw u := by
      intro x hx
      refine eq_of_continuousOn_int_valued (h := fun x => τu x - τw x)
        ((hVuord.inter hVword).isPreconnected) ?_ ?_ hx ⟨huVu, huVw⟩
      · exact (hVucont.mono inter_subset_left).sub (hVwcont.mono inter_subset_right)
      · intro y hy
        obtain ⟨m, hm⟩ := hmod (τu y) (τw y) (by rw [hVulift y hy.1, hVwlift y hy.2])
        exact ⟨m, by rw [hm]; push_cast; ring⟩
    set V : Set ℝ := Vu ∪ Vw with hVdef
    set G : ℝ → ℝ := Vu.piecewise τu (fun x => τw x + (k : ℝ)) with hGdef
    have hVopen : IsOpen V := hVuopen.union hVwopen
    have hVord : V.OrdConnected := ordConnected_union_of_mem hVuord hVword huVu huVw
    have hVJ : V ⊆ J := union_subset hVuJ hVwJ
    have hw₀V : w₀ ∈ V := Or.inl hw₀Vu
    have hwV : w ∈ V := Or.inr hwVw
    have hagree : ∀ x ∈ Vw, G x = τw x + (k : ℝ) := by
      intro x hx
      by_cases hxVu : x ∈ Vu
      · rw [hGdef, Set.piecewise_eq_of_mem _ _ _ hxVu]
        have h1 := hdiff x ⟨hxVu, hx⟩
        rw [hk] at h1
        linarith
      · rw [hGdef, Set.piecewise_eq_of_notMem _ _ _ hxVu]
    have hGcont : ContinuousOn G V := by
      rw [IsOpen.continuousOn_iff hVopen]
      intro a ha
      by_cases haVu : a ∈ Vu
      · have hev : G =ᶠ[𝓝 a] τu := by
          filter_upwards [hVuopen.mem_nhds haVu] with x hx
          exact Set.piecewise_eq_of_mem _ _ _ hx
        exact (hVucont.continuousAt (hVuopen.mem_nhds haVu)).congr hev.symm
      · have haVw : a ∈ Vw := by
          rw [hVdef] at ha
          rcases ha with h | h
          · exact absurd h haVu
          · exact h
        have hev : G =ᶠ[𝓝 a] (fun x => τw x + (k : ℝ)) := by
          filter_upwards [hVwopen.mem_nhds haVw] with x hx
          exact hagree x hx
        exact ((hVwcont.continuousAt (hVwopen.mem_nhds haVw)).add continuousAt_const).congr
          hev.symm
    have hGlift : ∀ x ∈ V, γ (G x) = α x := by
      intro x hx
      by_cases hxVu : x ∈ Vu
      · rw [hGdef, Set.piecewise_eq_of_mem _ _ _ hxVu]
        exact hVulift x hxVu
      · have hxVw : x ∈ Vw := by
          rw [hVdef] at hx
          rcases hx with h | h
          · exact absurd h hxVu
          · exact h
        rw [hGdef, Set.piecewise_eq_of_notMem _ _ _ hxVu, per_int hper (τw x) k]
        exact hVwlift x hxVw
    have hGanch : G w₀ = t₀ := by
      rw [hGdef, Set.piecewise_eq_of_mem _ _ _ hw₀Vu, hVuanch]
    exact ⟨hwJ, ⟨G w, V, G, hVJ, hVopen, hVord, hw₀V, hwV, hGcont, hGlift, hGanch, rfl⟩⟩
  have hJSS : J ⊆ S := by
    intro w hwJ
    by_contra hwS
    have hclopen : IsOpen (closure S)ᶜ := isClosed_closure.isOpen_compl
    have hsub : J ⊆ S ∪ (closure S)ᶜ := by
      intro x hxJ
      by_cases hxS : x ∈ S
      · exact Or.inl hxS
      · exact Or.inr (fun hxc => hxS (hkey x hxJ hxc))
    have h1 : (J ∩ S).Nonempty := ⟨w₀, hw₀, hw₀S⟩
    have h2 : (J ∩ (closure S)ᶜ).Nonempty :=
      ⟨w, hwJ, fun hc => hwS (hkey w hwJ hc)⟩
    obtain ⟨z, hzJ, hzS, hzcl⟩ := hJc S (closure S)ᶜ hSopen hclopen hsub h1 h2
    exact hzcl (subset_closure hzS)
  intro w hwJ
  exact (hJSS hwJ).2

/-- **The global continuous lift** along a preconnected piece of the level. -/
lemma exists_continuous_lift {γ α : ℝ → M} {J : Set ℝ} (hJ : IsOpen J)
    (hJc : IsPreconnected J) (hJα : ∀ w ∈ J, α w ∈ Set.range γ)
    (hmod : ∀ x y : ℝ, γ x = γ y → ∃ k : ℤ, x = y + k)
    (hper : ∀ x : ℝ, γ (x + 1) = γ x)
    (hpiece : ∀ (w : ℝ) (hw : w ∈ J) (t : ℝ), γ t = α w →
       ∃ (V : Set ℝ) (τ_V : ℝ → ℝ), V ⊆ J ∧ IsOpen V ∧ V.OrdConnected ∧ w ∈ V ∧
         ContinuousOn τ_V V ∧ (∀ u ∈ V, γ (τ_V u) = α u) ∧ τ_V w = t) :
    ∃ τ : ℝ → ℝ, ContinuousOn τ J ∧ ∀ w ∈ J, γ (τ w) = α w := by
  classical
  by_cases hne : J.Nonempty
  · obtain ⟨w₀, hw₀⟩ := hne
    obtain ⟨t₀, ht₀⟩ := hJα w₀ hw₀
    have hex : ∀ w ∈ J, ∃ v, AnchoredPiece γ α J w₀ t₀ w v :=
      anchoredPiece_exists hJ hJc hJα hmod hper hpiece hw₀ ht₀
    choose τf hτf using hex
    let τ : ℝ → ℝ := fun w => if h : w ∈ J then τf w h else 0
    have hτ : ∀ w (hw : w ∈ J), AnchoredPiece γ α J w₀ t₀ w (τ w) := by
      intro w hw
      change AnchoredPiece γ α J w₀ t₀ w (if h : w ∈ J then τf w h else 0)
      rw [dif_pos hw]
      exact hτf w hw
    refine ⟨τ, ?_, ?_⟩
    · rw [IsOpen.continuousOn_iff hJ]
      intro w hw
      obtain ⟨V, τV, hVJ, hVopen, hVord, hw₀V, hwV, hVcont, hVlift, hVanch, hVw⟩ := hτ w hw
      have heq : ∀ u ∈ V, τ u = τV u := by
        intro u hu
        exact anchoredPiece_uniq hmod (hτ u (hVJ hu))
          ⟨V, τV, hVJ, hVopen, hVord, hw₀V, hu, hVcont, hVlift, hVanch, rfl⟩
      refine (hVcont.continuousAt (hVopen.mem_nhds hwV)).congr ?_
      filter_upwards [hVopen.mem_nhds hwV] with u hu
      exact (heq u hu).symm
    · intro w hw
      obtain ⟨V, τV, hVJ, hVopen, hVord, hw₀V, hwV, hVcont, hVlift, hVanch, hVw⟩ := hτ w hw
      rw [← hVw]
      exact hVlift w hwV
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact continuousOn_empty _
    · intro w hw
      rw [Set.not_nonempty_iff_eq_empty.mp hne] at hw
      simp at hw

/-- A continuous lift of `α` along the periodic curve `γ` is `C^∞`: locally it is the local phase
of `γ` composed with `α`. -/
lemma contDiffOn_of_lift {γ α : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ,ℝ) (𝓡 2) Cinf γ)
    (himm : ∀ t : ℝ, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t 1 ≠ 0)
    (hα : ContMDiff 𝓘(ℝ,ℝ) (𝓡 2) Cinf α) {J : Set ℝ} (hJ : IsOpen J) {τ : ℝ → ℝ}
    (hτc : ContinuousOn τ J) (hcast : ∀ w ∈ J, γ (τ w) = α w) :
    ContDiffOn ℝ Cinf τ J := by
  rw [IsOpen.contDiffOn_iff hJ]
  intro w hw
  obtain ⟨U, φ, hUopen, hγtU, hφsm, δ, hδpos, hφ⟩ :=
    Work.Drive.N2C.exists_localPhase_of_immersed_curve γ hγsm himm (τ w)
  have hαwU : α w ∈ U := by rw [← hcast w hw]; exact hγtU
  have hτat : ContinuousAt τ w := hτc.continuousAt (hJ.mem_nhds hw)
  have hV1 : {w' : ℝ | α w' ∈ U} ∈ 𝓝 w :=
    hα.continuous.continuousAt.preimage_mem_nhds (hUopen.mem_nhds hαwU)
  have hV2 : {w' : ℝ | τ w' ∈ Ioo (τ w - δ) (τ w + δ)} ∈ 𝓝 w :=
    hτat.preimage_mem_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  have hcomp : ContDiffAt ℝ Cinf (fun w' => φ (α w')) w :=
    contMDiffAt_iff_contDiffAt.mp ((hφsm.contMDiffAt (hUopen.mem_nhds hαwU)).comp w
      hα.contMDiffAt)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hV1, hV2, hJ.mem_nhds hw] with w' h1 h2 h3
  have := hφ (τ w') h2
  rw [hcast w' h3] at this
  exact this.symm

/-- The derivative of a lift does not vanish: the chain rule writes `mfderiv α w 1` as a multiple
of the (nonzero) `mfderiv γ (τ w) 1`. -/
lemma deriv_ne_zero_of_lift {γ α : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ,ℝ) (𝓡 2) Cinf γ)
    (hαimm : ∀ w : ℝ, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) α w 1 ≠ 0)
    {J : Set ℝ} (hJ : IsOpen J) {τ : ℝ → ℝ} (hτsm : ContDiffOn ℝ Cinf τ J)
    (hcast : ∀ w ∈ J, γ (τ w) = α w) :
    ∀ w ∈ J, deriv τ w ≠ 0 := by
  intro w hw
  have hτat : ContDiffAt ℝ Cinf τ w := (IsOpen.contDiffOn_iff hJ).mp hτsm hw
  have hτmd : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) τ w :=
    (contMDiffAt_iff_contDiffAt.mpr hτat).mdifferentiableAt (by simp)
  have hγmd : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) γ (τ w) :=
    (hγsm.contMDiffAt (x := τ w)).mdifferentiableAt (by simp)
  have hchain : mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ ∘ τ) w
      = (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ (τ w)).comp (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) τ w) :=
    mfderiv_comp w hγmd hτmd
  have hev : (γ ∘ τ) =ᶠ[𝓝 w] α := by
    filter_upwards [hJ.mem_nhds hw] with x hx
    exact hcast x hx
  have hchain' : mfderiv 𝓘(ℝ,ℝ) (𝓡 2) α w
      = (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ (τ w)).comp (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) τ w) := by
    rw [← Filter.EventuallyEq.mfderiv_eq_v433 hev]
    exact hchain
  have h1 : (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) τ w) 1 = deriv τ w := by
    rw [mfderiv_eq_fderiv]
    rfl
  have happ : mfderiv 𝓘(ℝ,ℝ) (𝓡 2) α w 1
      = (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ (τ w)) (deriv τ w) := by
    rw [hchain']
    change (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ (τ w)) ((mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) τ w) 1)
      = (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ (τ w)) (deriv τ w)
    exact congrArg _ h1
  intro h0
  have h0' : (deriv τ w : TangentSpace 𝓘(ℝ,ℝ) (τ w)) = 0 := h0
  rw [h0', map_zero] at happ
  exact hαimm w happ

/-- A `C^∞` function on a preconnected open set with nowhere vanishing derivative is strictly
monotone (increasing or decreasing). -/
lemma strictMonoOn_or_strictAntiOn_of_deriv_ne_zero {J : Set ℝ} {τ : ℝ → ℝ} (hJ : IsOpen J)
    (hJc : IsPreconnected J) (hτsm : ContDiffOn ℝ Cinf τ J) (hne : ∀ w ∈ J, deriv τ w ≠ 0) :
    StrictMonoOn τ J ∨ StrictAntiOn τ J := by
  have hdcont : ContinuousOn (deriv τ) J :=
    hτsm.continuousOn_deriv_of_isOpen hJ (by simp)
  have hu : IsOpen (J ∩ (deriv τ) ⁻¹' Iio 0) := hdcont.isOpen_inter_preimage hJ isOpen_Iio
  have hv : IsOpen (J ∩ (deriv τ) ⁻¹' Ioi 0) := hdcont.isOpen_inter_preimage hJ isOpen_Ioi
  have hdisj : Disjoint (J ∩ (deriv τ) ⁻¹' Iio 0) (J ∩ (deriv τ) ⁻¹' Ioi 0) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : deriv τ x < 0 := hx.2
    have h2 : 0 < deriv τ x := hx'.2
    exact absurd h1 (not_lt.mpr (le_of_lt h2))
  have hsub : J ⊆ (J ∩ (deriv τ) ⁻¹' Iio 0) ∪ (J ∩ (deriv τ) ⁻¹' Ioi 0) := by
    intro x hx
    rcases lt_or_gt_of_ne (hne x hx) with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hconv : Convex ℝ J := convex_iff_ordConnected.mpr hJc.ordConnected
  rcases hJc.subset_or_subset hu hv hdisj hsub with h | h
  · right
    exact strictAntiOn_of_deriv_neg hconv hτsm.continuousOn (fun x hx => by
      rw [hJ.interior_eq] at hx; exact (h hx).2)
  · left
    exact strictMonoOn_of_deriv_pos hconv hτsm.continuousOn (fun x hx => by
      rw [hJ.interior_eq] at hx; exact (h hx).2)

open scoped Manifold ContDiff Topology in
/-- **A curve inside one component of a level lifts to the parameter of the component** (§1.3 of
`N2Lead/NOTES_LEAD_saddlePacket.md`).

If `α : ℝ → M` is a smooth immersion (injectivity of its differential against `1`) whose image on an
open preconnected `J` lies in the range of the `i`-th component curve `L.γ i` of a `LevelCurves`
parametrisation of the level `f = b`, then there is a smooth parameter change `τ` on `J` with
`L.γ i (τ w) = α w`, nonvanishing derivative, and `τ` is *either* strictly increasing or strictly
decreasing — the last row is what decides split versus Möbius in the saddle packet (the two pinned
arcs are lifted into their common component and compared by the sign of `τ'`).

Route (per the note): `γ i` factors through `AddCircle 1` as a continuous bijection from a compact
space onto a Hausdorff subspace, hence is a homeomorphism onto its range; lift the path `α|_J`
through the covering `ℝ → AddCircle 1`; smoothness of `τ` locally from the local phase of the
immersed curve (`Work.Drive.N2C.exists_localPhase_of_immersed_curve`); `τ' ≠ 0` from `hαimm` by the
chain rule; the constant sign of `τ'` on the preconnected (hence interval) `J` from the intermediate
value theorem.  (The formalisation below replaces the covering-theoretic lift by the equivalent
explicit local-to-global gluing of `AnchoredPiece`s along the interval `J`.) -/
theorem exists_arcLift {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {b : ℝ} {n : ℕ} (L : Work.Drive.N2C.LevelCurves f b n) (i : Fin n)
    {α : ℝ → M} (hα : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) α)
    (hαimm : ∀ w : ℝ, mfderiv 𝓘(ℝ, ℝ) (𝓡 2) α w 1 ≠ 0)
    {J : Set ℝ} (hJ : IsOpen J) (hJc : IsPreconnected J)
    (hJα : ∀ w ∈ J, α w ∈ Set.range (L.γ i)) :
    ∃ τ : ℝ → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ J ∧
      (∀ w ∈ J, L.γ i (τ w) = α w) ∧
      (∀ w ∈ J, deriv τ w ≠ 0) ∧ (StrictMonoOn τ J ∨ StrictAntiOn τ J) := by
  have himm : ∀ t : ℝ, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) t 1 ≠ 0 :=
    fun t => mfderiv_γ_ne_zero L i t
  have hpiece : ∀ (w : ℝ) (hw : w ∈ J) (t : ℝ), L.γ i t = α w →
      ∃ (V : Set ℝ) (τ_V : ℝ → ℝ), V ⊆ J ∧ IsOpen V ∧ V.OrdConnected ∧ w ∈ V ∧
        ContinuousOn τ_V V ∧ (∀ u ∈ V, L.γ i (τ_V u) = α u) ∧ τ_V w = t :=
    fun w hw t ht => exists_local_piece_of L i hα himm hJ hJc hJα w hw t ht
  obtain ⟨τ, hτc, hτγ⟩ :=
    exists_continuous_lift hJ hJc hJα (L.modOne i) (L.per i) hpiece
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ J :=
    contDiffOn_of_lift (L.sm i) himm hα hJ hτc hτγ
  have hderiv : ∀ w ∈ J, deriv τ w ≠ 0 :=
    deriv_ne_zero_of_lift (L.sm i) hαimm hJ hsm hτγ
  have hmono : StrictMonoOn τ J ∨ StrictAntiOn τ J :=
    strictMonoOn_or_strictAntiOn_of_deriv_ne_zero hJ hJc hsm hderiv
  exact ⟨τ, hsm, hτγ, hderiv, hmono⟩

end Work.Drive.N2Lead

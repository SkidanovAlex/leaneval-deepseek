import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLComp.isOpenMap_smul
import Submission.Work.EKLContract.Lemmas.V_open_one

/-!
# Uniform injectivity of the `SL₃(ℝ)`-action on `X₃ = SL₃(ℝ)/SL₃(ℤ)` near the identity

For a compact set `K ⊆ X₃` there is `δ > 0` such that two elements `g, h` of the displacement
neighbourhood `V δ` (matrices within `δ` of the identity, entrywise) that move the same point
`x ∈ K` to the same point are equal: `g • x = h • x → g = h`.

Equivalently, the action map is injective in the group variable on a neighbourhood of the
identity, uniformly over `K`.  The proof is the classical one: `Γ₃ = SL₃(ℤ)` is discrete, so
the quotient map `SL₃(ℝ) → X₃` is injective on a small neighbourhood of the identity;
conjugating by the stabiliser of a point of `K` gives injectivity near that point, and
compactness makes it uniform.  The compactness step is implemented with an ultrafilter refining
`atTop`: this replaces "finitely many points of `K`" by a single limit point `x ∈ K` and its
stabiliser.
-/

namespace Work.EKLComp

open Work.EKLContract
open Filter Topology

set_option linter.unusedVariables false

/-- `V` is monotone in its parameter. -/
lemma V_subset_of_le {δ ε : ℝ} (h : δ ≤ ε) : V δ ⊆ V ε := fun _ hg i j => lt_of_lt_of_le (hg i j) h

/-- A finite set of positive reals has a positive lower bound. -/
lemma exists_pos_le_of_finset (s : Finset ℝ) (h : ∀ x ∈ s, 0 < x) :
    ∃ δ, 0 < δ ∧ ∀ x ∈ s, δ ≤ x := by
  induction s using Finset.induction with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
      obtain ⟨δ, hδ, hδle⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
      rcases le_total δ a with hle | hle
      · exact ⟨δ, hδ, fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hle
          · exact hδle x hx⟩
      · exact ⟨a, h a (Finset.mem_insert_self a s), fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact le_rfl
          · exact hle.trans (hδle x hx)⟩

/-- In a finite product of copies of `ℝ` (here the space of `3 × 3` matrices) the entrywise
sup-balls form a neighbourhood basis at every point. -/
lemma pi_ball_basis (f : Fin 3 → Fin 3 → ℝ) : ∀ u ∈ nhds f, ∃ δ > 0,
    Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => Metric.ball (f i j) δ)) ⊆ u := by
  intro u hu
  have hu' : u ∈ Filter.pi (fun i : Fin 3 => nhds (f i)) := by rwa [nhds_pi] at hu
  obtain ⟨I, t, ht, htu⟩ := Filter.mem_pi'.mp hu'
  have h2 : ∀ i, ∃ c : Fin 3 → Set ℝ, (∀ j, c j ∈ nhds (f i j)) ∧
      Set.pi Set.univ c ⊆ t i := by
    intro i
    have hi : t i ∈ Filter.pi (fun j : Fin 3 => nhds (f i j)) := by
      have := ht i
      rwa [nhds_pi] at this
    obtain ⟨J, c, hc, hcsub⟩ := Filter.mem_pi'.mp hi
    exact ⟨c, hc, fun b hb => hcsub fun j _ => hb j (Set.mem_univ j)⟩
  choose c hc hcsub using h2
  have h3 : ∀ i j, ∃ ε > 0, Metric.ball (f i j) ε ⊆ c i j := fun i j =>
    Metric.mem_nhds_iff.mp (hc i j)
  choose ε hεpos hεsub using h3
  obtain ⟨δ, hδpos, hδle⟩ := exists_pos_le_of_finset
    ((Finset.univ : Finset (Fin 3 × Fin 3)).image (fun p => ε p.1 p.2)) (fun x hx => by
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hx
      exact hεpos p.1 p.2)
  refine ⟨δ, hδpos, fun b hb => htu ?_⟩
  refine fun i _ => hcsub i fun j _ => hεsub i j ?_
  exact lt_of_lt_of_le (hb i (Set.mem_univ i) j (Set.mem_univ j))
    (hδle (ε i j) (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))

/-- The sets `V δ` form a neighbourhood basis of the identity of `SL₃(ℝ)`: this is the statement
that the topology of `SL₃(ℝ)` is the subspace topology inherited from the matrix space, where
`V δ` is the entrywise sup-box of radius `δ`. -/
lemma V_nhds_hasBasis : (nhds (1 : SL3)).HasBasis (fun δ : ℝ => 0 < δ) V := by
  rw [Filter.hasBasis_iff]
  intro t
  constructor
  · intro ht
    obtain ⟨s, hst, hsopen, hs1⟩ := mem_nhds_iff.mp ht
    obtain ⟨u, huopen, hueq⟩ := isOpen_induced_iff.mp hsopen
    have hmem_u : (((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) ∈ u := by
      have h : (1 : SL3) ∈ s := hs1
      rw [hueq.symm] at h
      exact Set.mem_preimage.mp h
    obtain ⟨δ, hδpos, hδsub⟩ := pi_ball_basis _ u (huopen.mem_nhds hmem_u)
    refine ⟨δ, hδpos, fun g hg => hst ?_⟩
    rw [hueq.symm]
    exact Set.mem_preimage.mpr (hδsub fun i _ j _ => by
      rw [Metric.mem_ball, Real.dist_eq]
      simpa using hg i j)
  · rintro ⟨δ, hδ, hsub⟩
    exact Filter.mem_of_superset
      ((Work.EKLContract.Lemmas.V_open_one δ hδ).1.mem_nhds
        (Work.EKLContract.Lemmas.V_open_one δ hδ).2) hsub

theorem uniform_injective_V : ∀ K : Set Work.EKLContract.X3, IsCompact K → ∃ δ > 0, ∀ x ∈ K, ∀ g ∈ Work.EKLContract.V δ, ∀ h ∈ Work.EKLContract.V δ, g • x = h • x → g = h := by
  intro K hK
  -- suppose the statement fails for every `δ > 0`; choose a bad configuration at scale
  -- `1/(n+1)` for every `n`
  by_contra hbad
  push Not at hbad
  choose x hxK g hgV h hhV heq hne using fun n : ℕ => hbad (1 / ((n : ℝ) + 1)) (by positivity)
  -- an ultrafilter refining `atTop`; along it every sequence tending to `1` does so
  obtain ⟨u, hu⟩ := Filter.exists_ultrafilter_le (Filter.atTop : Filter ℕ)
  -- compactness of `K` gives a limit point `x₀ ∈ K` of `x` along `u`
  have hle : (u.map x : Filter X3) ≤ 𝓟 K := by
    rw [Ultrafilter.coe_map, Filter.le_principal_iff, Filter.mem_map]
    exact Filter.Eventually.of_forall hxK
  obtain ⟨x₀, hx₀K, hx₀lim⟩ := isCompact_iff_ultrafilter_le_nhds.mp hK (u.map x) hle
  have htend : Tendsto x (u : Filter ℕ) (𝓝 x₀) := by
    simpa [Filter.Tendsto, Ultrafilter.coe_map] using hx₀lim
  -- write `x₀ = mkX g₀`
  obtain ⟨g₀, rfl⟩ : ∃ g₀ : SL3, mkX g₀ = x₀ := QuotientGroup.mk_surjective x₀
  -- `Γ₃` is discrete: an open neighbourhood `W` of the identity meeting `Γ₃` only at `1`
  obtain ⟨W, hWopen, hW1, hW⟩ := Work.EKLContract.Lemmas.exists_open_injective_Γ3
  have hWΓ : W ∩ (Γ3 : Set SL3) ⊆ ({1} : Set SL3) := by
    intro ζ hζ
    exact Set.mem_singleton_iff.mpr (hW 1 hW1 ζ hζ.1 (by simpa using hζ.2)).symm
  -- neighbourhoods `A ∋ g₀`, `B ∋ 1` with `w⁻¹ σ w ∈ W` for `w ∈ A`, `σ ∈ B`
  have hΨcont : Continuous fun p : SL3 × SL3 => p.1⁻¹ * p.2 * p.1 := by fun_prop
  have hΨev : ∀ᶠ p : SL3 × SL3 in (𝓝 g₀) ×ˢ (𝓝 (1 : SL3)), p.1⁻¹ * p.2 * p.1 ∈ W := by
    have hpt : (fun p : SL3 × SL3 => p.1⁻¹ * p.2 * p.1) (g₀, (1 : SL3)) = 1 := by group
    have hmem : W ∈ 𝓝 ((fun p : SL3 × SL3 => p.1⁻¹ * p.2 * p.1) (g₀, (1 : SL3))) := by
      rw [hpt]; exact hWopen.mem_nhds hW1
    have h := hΨcont.continuousAt.preimage_mem_nhds hmem
    rwa [nhds_prod_eq] at h
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.eventually_prod_iff.mp hΨev
  have hA' : {z : SL3 | A z} ∈ 𝓝 g₀ := hA
  have hB' : {z : SL3 | B z} ∈ 𝓝 (1 : SL3) := hB
  -- neighbourhoods `A₁, A₂ ∋ 1` with `g⁻¹ h ∈ B` for `g ∈ A₁`, `h ∈ A₂`
  have hΦcont : Continuous fun p : SL3 × SL3 => p.1⁻¹ * p.2 := by fun_prop
  have hΦev : ∀ᶠ p : SL3 × SL3 in (𝓝 (1:SL3)) ×ˢ (𝓝 (1 : SL3)), p.1⁻¹ * p.2 ∈ {z : SL3 | B z} := by
    have hpt : (fun p : SL3 × SL3 => p.1⁻¹ * p.2) ((1:SL3), (1 : SL3)) = 1 := by group
    have hmem : {z : SL3 | B z} ∈ 𝓝 ((fun p : SL3 × SL3 => p.1⁻¹ * p.2) ((1:SL3), (1 : SL3))) := by
      rw [hpt]; exact hB'
    have h := hΦcont.continuousAt.preimage_mem_nhds hmem
    rwa [nhds_prod_eq] at h
  obtain ⟨A₁, hA₁, A₂, hA₂, hA₁₂⟩ := Filter.eventually_prod_iff.mp hΦev
  have hA₁' : {z : SL3 | A₁ z} ∈ 𝓝 (1 : SL3) := hA₁
  have hA₂' : {z : SL3 | A₂ z} ∈ 𝓝 (1 : SL3) := hA₂
  -- an open neighbourhood `M ∋ 1` with `M * g₀ ⊆ A`
  have hMev : {z : SL3 | A (z * g₀)} ∈ 𝓝 (1 : SL3) := by
    have hcont : Continuous fun z : SL3 => z * g₀ := by fun_prop
    have hpt : (fun z : SL3 => z * g₀) (1 : SL3) = g₀ := by group
    have hmem : {z : SL3 | A z} ∈ 𝓝 ((fun z : SL3 => z * g₀) (1 : SL3)) := by
      rw [hpt]; exact hA'
    exact hcont.continuousAt.preimage_mem_nhds hmem
  obtain ⟨M, hMsub, hMopen, hM1⟩ := mem_nhds_iff.mp hMev
  obtain ⟨δ₁, hδ₁, hV₁⟩ := V_nhds_hasBasis.mem_iff.mp hA₁'
  obtain ⟨δ₂, hδ₂, hV₂⟩ := V_nhds_hasBasis.mem_iff.mp hA₂'
  set δ₀ := min δ₁ δ₂ with hδ₀def
  have hδ₀pos : 0 < δ₀ := lt_min hδ₁ hδ₂
  have hδ₀le₁ : δ₀ ≤ δ₁ := by rw [hδ₀def]; exact min_le_left _ _
  have hδ₀le₂ : δ₀ ≤ δ₂ := by rw [hδ₀def]; exact min_le_right _ _
  have hVδ₀ : V δ₀ ∈ 𝓝 (1 : SL3) := V_nhds_hasBasis.mem_of_mem hδ₀pos
  -- `g n → 1` and `h n → 1` along the ultrafilter
  have hg_tend : Tendsto g (u : Filter ℕ) (𝓝 (1 : SL3)) := by
    rw [V_nhds_hasBasis.tendsto_right_iff]
    intro δ hδ
    have hsmall : ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ), (1:ℝ) / ((n:ℝ) + 1) < δ :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hδ
    filter_upwards [hu hsmall] with n hn
    exact V_subset_of_le (le_of_lt hn) (hgV n)
  have hh_tend : Tendsto h (u : Filter ℕ) (𝓝 (1 : SL3)) := by
    rw [V_nhds_hasBasis.tendsto_right_iff]
    intro δ hδ
    have hsmall : ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ), (1:ℝ) / ((n:ℝ) + 1) < δ :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hδ
    filter_upwards [hu hsmall] with n hn
    exact V_subset_of_le (le_of_lt hn) (hhV n)
  -- the open neighbourhood `O` of `x₀ = mkX g₀` of the `M`-translates of `x₀`
  let O : Set X3 := (fun z : SL3 => z • mkX g₀) '' M
  have hOopen : IsOpen O := isOpenMap_smul (mkX g₀) M hMopen
  have hx₀O : mkX g₀ ∈ O := ⟨1, hM1, one_smul SL3 (mkX g₀)⟩
  have hevO : ∀ᶠ n in (u : Filter ℕ), x n ∈ O := htend.eventually (hOopen.mem_nhds hx₀O)
  have hAll : ∀ᶠ n in (u : Filter ℕ), (x n ∈ O ∧ g n ∈ V δ₀ ∧ h n ∈ V δ₀) :=
    hevO.and ((hg_tend.eventually hVδ₀).and (hh_tend.eventually hVδ₀))
  -- choose `n` at which all the good properties hold simultaneously
  obtain ⟨n, hnO, hng, hnh⟩ := hAll.exists
  obtain ⟨uₙ, huₙM, huₙ⟩ := hnO
  have hwA : A (uₙ * g₀) := hMsub huₙM
  have hσB : B ((g n)⁻¹ * h n) :=
    hA₁₂ (hV₁ (V_subset_of_le hδ₀le₁ hng)) (hV₂ (V_subset_of_le hδ₀le₂ hnh))
  have hWζ : (uₙ * g₀)⁻¹ * ((g n)⁻¹ * h n) * (uₙ * g₀) ∈ W := hAB hwA hσB
  -- the coset computation
  have h1 : g n • x n = mkX (g n * uₙ * g₀) := by
    rw [← huₙ, ← mul_smul]
    rfl
  have h2 : h n • x n = mkX (h n * uₙ * g₀) := by
    rw [← huₙ, ← mul_smul]
    rfl
  have hcoset : (g n * uₙ * g₀)⁻¹ * (h n * uₙ * g₀) ∈ Γ3 := by
    refine QuotientGroup.eq.mp ?_
    change mkX (g n * uₙ * g₀) = mkX (h n * uₙ * g₀)
    rw [← h1, ← h2, heq]
  have hζΓ : (uₙ * g₀)⁻¹ * ((g n)⁻¹ * h n) * (uₙ * g₀) ∈ Γ3 := by
    rw [show (uₙ * g₀)⁻¹ * ((g n)⁻¹ * h n) * (uₙ * g₀)
        = (g n * uₙ * g₀)⁻¹ * (h n * uₙ * g₀) by group]
    exact hcoset
  have hζ1 : (uₙ * g₀)⁻¹ * ((g n)⁻¹ * h n) * (uₙ * g₀) = 1 := by
    have hmem := hWΓ ⟨hWζ, hζΓ⟩
    simpa using hmem
  have hσ1 : (g n)⁻¹ * h n = 1 := by
    calc (g n)⁻¹ * h n
        = (uₙ * g₀) * ((uₙ * g₀)⁻¹ * ((g n)⁻¹ * h n) * (uₙ * g₀)) * (uₙ * g₀)⁻¹ := by group
      _ = 1 := by rw [hζ1]; group
  have hgh : g n = h n := by
    calc g n = g n * 1 := by group
      _ = g n * ((g n)⁻¹ * h n) := by rw [hσ1]
      _ = h n := by group
  exact hne n hgh

end Work.EKLComp

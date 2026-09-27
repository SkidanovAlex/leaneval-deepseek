import Mathlib
import Submission.Work.Whitney.PathTools.TotallyDisconnectedPlane

/-!
# A compact totally disconnected subset of `ℝ^m` (`m ≥ 2`) does not separate

Target: `Work.Whitney.PathTools.compl_totallyDisconnected_pathConnected`.

The planar theorem (`TotallyDisconnectedPlane.lean`) is transported to `ℝ^m` along the linear
isometry `ℝ² → ℝ^m` spanned by an orthonormal pair `(u, w)` with `u` along `Y - X` and `w ⊥ u`
(`plane_transport.lean`, `joinedIn_compl_of_isometry`).
-/

namespace Work.Whitney.PathTools

open Set Metric Topology
open scoped InnerProductSpace

variable {m : ℕ}

/-- A compact subset of `ℝ^m` (`m ≥ 1`) is not everything. -/
theorem exists_notMem_euclidean {n : ℕ} (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) : ∃ z, z ∉ K := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin n))).mp
    hK.isBounded
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    ⟨0, (WithLp.equiv 2 (Fin n → ℝ)).symm (Pi.single ⟨0, by omega⟩ 1), by
      intro h
      have h1 := congrFun (congrArg (WithLp.equiv 2 (Fin n → ℝ)) h) ⟨0, by omega⟩
      simp at h1⟩
  obtain ⟨w, hw⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  refine ⟨((|R| + 1) / ‖w‖) • w, ?_⟩
  intro hmem
  have h1 := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity),
    div_mul_cancel₀ _ (ne_of_gt hwn)] at h1
  have h2 := le_abs_self R
  linarith

/-- In any real inner product space of dimension at least two, a nonzero vector has a unit vector
orthogonal to it. -/
theorem exists_unit_orthogonal_general {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hE : 2 ≤ Module.finrank ℝ E) {v : E} (hv : v ≠ 0) :
    ∃ w : E, ‖w‖ = 1 ∧ inner ℝ v w = 0 := by
  haveI : Fact (Module.finrank ℝ E = (Module.finrank ℝ E - 1) + 1) := ⟨by omega⟩
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E - 1)) ℝ ↥(ℝ ∙ v)ᗮ :=
    OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (n := Module.finrank ℝ E - 1) hv
  have hpos : 0 < Module.finrank ℝ E - 1 := by omega
  refine ⟨((b ⟨0, hpos⟩ : ↥(ℝ ∙ v)ᗮ) : E), ?_, ?_⟩
  · rw [← Submodule.coe_norm]
    exact (b.orthonormal).1 ⟨0, hpos⟩
  · have hmem : ((b ⟨0, hpos⟩ : ↥(ℝ ∙ v)ᗮ) : E) ∈ (ℝ ∙ v)ᗮ := (b ⟨0, hpos⟩).2
    exact (Submodule.mem_orthogonal (ℝ ∙ v) _).mp hmem v (Submodule.mem_span_singleton_self v)

/-- In `ℝⁿ` with `n ≥ 2`, a nonzero vector has a unit vector orthogonal to it. -/
theorem exists_unit_orthogonal {n : ℕ} (hn : 2 ≤ n) {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ≠ 0) : ∃ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 ∧ inner ℝ v w = 0 :=
  exists_unit_orthogonal_general (E := EuclideanSpace ℝ (Fin n))
    (by rw [finrank_euclideanSpace_fin]; omega) hv

/-- **Sierpiński's theorem transported along an isometry.**  Let `φ : ℝ² → E` be an isometry and
`K ⊆ E` compact and totally disconnected.  If `x` and `y` lie in the image of `φ` and outside `K`,
they can be joined by a path that stays in the image of `φ` and avoids `K`. -/
theorem joinedIn_compl_of_isometry {E : Type*} [MetricSpace E] {φ : Grid.Pt → E}
    (hφ : Isometry φ) (hφc : Continuous φ) {K : Set E} (hK : IsCompact K)
    (htd : IsTotallyDisconnected K) {x y : E} (hx : x ∉ K) (hy : y ∉ K)
    (hxc : ∃ t, φ t = x) (hyc : ∃ t, φ t = y) : JoinedIn (Kᶜ ∩ Set.range φ) x y := by
  obtain ⟨tx, rfl⟩ := hxc
  obtain ⟨ty, rfl⟩ := hyc
  have hinj : Function.Injective φ := by
    intro s t hst
    have h1 : dist (φ s) (φ t) = dist s t := hφ.dist_eq s t
    rw [hst, dist_self] at h1
    exact dist_eq_zero.mp h1.symm
  have hK'c : IsCompact (φ ⁻¹' K) := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨hK.isClosed.preimage hφc, ?_⟩
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (φ tx)).mp hK.isBounded
    refine (Metric.isBounded_iff_subset_closedBall tx).mpr ⟨R, ?_⟩
    intro t ht
    rw [Metric.mem_closedBall]
    have h1 : φ t ∈ Metric.closedBall (φ tx) R := hR ht
    rw [Metric.mem_closedBall] at h1
    rwa [hφ.dist_eq t tx] at h1
  have htd' : IsTotallyDisconnected (φ ⁻¹' K) := by
    intro P hPK hPpre
    have himg : IsPreconnected (φ '' P) := hPpre.image φ hφc.continuousOn
    have hsub : φ '' P ⊆ K := fun z ⟨t, ht, htz⟩ => htz ▸ hPK ht
    have hsing : (φ '' P).Subsingleton := htd _ hsub himg
    intro a ha b hb
    exact hinj (hsing ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)
  obtain ⟨γ, hγ⟩ := (Grid.compl_totallyDisconnected_plane hK'c htd').joinedIn tx
    (by simpa [Set.mem_compl_iff, Set.mem_preimage] using hx) ty
    (by simpa [Set.mem_compl_iff, Set.mem_preimage] using hy)
  refine ⟨γ.map hφc, ?_⟩
  intro t
  exact ⟨hγ t, ⟨γ t, rfl⟩⟩

/-- The linear isometry `ℝ² → E` spanned by an orthonormal pair. -/
theorem exists_linearIsometry_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u w : E} (hu : ‖u‖ = 1) (hw1 : ‖w‖ = 1) (hw2 : ⟪u, w⟫_ℝ = 0) :
    ∃ Φ : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] E, ∀ p, Φ p = p 0 • u + p 1 • w := by
  let L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] E :=
    { toFun := fun p => p 0 • u + p 1 • w
      map_add' := by
        intro p q
        simp only [PiLp.add_apply, add_smul]
        abel
      map_smul' := by
        intro c p
        simp only [PiLp.smul_apply, smul_add, smul_smul, RingHom.id_apply]
        congr 1 <;> rw [mul_comm] }
  have hLn : ∀ p, ‖L p‖ = ‖p‖ := by
    intro p
    have hcross : ⟪p 0 • u, p 1 • w⟫_ℝ = 0 := by
      rw [inner_smul_left, inner_smul_right, hw2, mul_zero]
      simp
    have hx : ‖p 0 • u‖ = |p 0| := by rw [norm_smul, Real.norm_eq_abs, hu, mul_one]
    have hy : ‖p 1 • w‖ = |p 1| := by rw [norm_smul, Real.norm_eq_abs, hw1, mul_one]
    have hpn : ‖p‖ = Real.sqrt ((p 0) ^ 2 + (p 1) ^ 2) := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
      congr 1
      norm_num
    have hsq : ‖L p‖ ^ 2 = ‖p‖ ^ 2 := by
      have hpy : ‖L p‖ ^ 2 = ‖p 0 • u‖ ^ 2 + ‖p 1 • w‖ ^ 2 := by
        have hLp : L p = p 0 • u + p 1 • w := rfl
        rw [hLp, norm_add_sq_real, hcross]; ring
      rw [hpy, hx, hy, hpn]
      rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (p 0) ^ 2 + (p 1) ^ 2)]
      rw [sq_abs, sq_abs]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · have hz : ‖p‖ = 0 := by linarith [norm_nonneg p, norm_nonneg (L p)]
      have hL0 : ‖L p‖ = 0 := by rw [h, hz, neg_zero]
      rw [hL0, hz]
  exact ⟨LinearIsometry.mk L hLn, fun p => rfl⟩

/-- The complement of a compact totally disconnected set in `ℝ^m`, `m ≥ 2`, is path connected. -/
theorem compl_totallyDisconnected_pathConnected {m : ℕ} (hm : 2 ≤ m)
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : IsCompact K) (htd : IsTotallyDisconnected K) :
    IsPathConnected (Kᶜ) := by
  classical
  obtain ⟨x₀, hx₀⟩ := exists_notMem_euclidean (n := m) (by omega) hK
  refine ⟨x₀, hx₀, fun Y hY => ?_⟩
  by_cases hXY : Y = x₀
  · subst hXY
    exact JoinedIn.refl (by simpa using hx₀)
  -- a unit vector along `Y - x₀`, and a unit vector orthogonal to it
  have hv : Y - x₀ ≠ 0 := sub_ne_zero.mpr hXY
  set u : EuclideanSpace ℝ (Fin m) := ‖Y - x₀‖⁻¹ • (Y - x₀) with hudef
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_smul, Real.norm_of_nonneg (by positivity),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  obtain ⟨w, hw1, hw2⟩ :=
    exists_unit_orthogonal (n := m) hm (v := u) (by intro h; rw [h, norm_zero] at hu; norm_num at hu)
  obtain ⟨Φ, hΦ⟩ := exists_linearIsometry_pair hu hw1 hw2
  -- the 2-plane parametrisation
  set φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m) := fun p => x₀ + Φ p with hφdef
  have hφiso : Isometry φ := by
    rw [isometry_iff_dist_eq]
    intro p q
    rw [hφdef]
    simp only
    rw [dist_add_left, Φ.isometry.dist_eq]
  have hφcont : Continuous φ := by
    rw [hφdef]
    exact continuous_const.add Φ.continuous
  -- the two points lie in the image
  have hxmem : ∃ t, φ t = x₀ := ⟨0, by rw [hφdef]; simp⟩
  set e₁ : EuclideanSpace ℝ (Fin 2) :=
    (WithLp.equiv 2 (Fin 2 → ℝ)).symm (Pi.single (0 : Fin 2) 1) with he₁def
  have he₁_0 : e₁ 0 = 1 := by simp [he₁def]
  have he₁_1 : e₁ 1 = 0 := by simp [he₁def]
  have hΦe₁ : Φ e₁ = u := by
    rw [hΦ]; simp only [he₁_0, he₁_1, one_smul, zero_smul, add_zero]
  have hymem : ∃ t, φ t = Y := by
    refine ⟨‖Y - x₀‖ • e₁, ?_⟩
    have h1 : Φ (‖Y - x₀‖ • e₁) = ‖Y - x₀‖ • u := by
      rw [map_smul, hΦe₁]
    show x₀ + Φ (‖Y - x₀‖ • e₁) = Y
    rw [h1, hudef, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
    abel
  -- apply the transported planar theorem
  obtain ⟨γ, hγ⟩ := joinedIn_compl_of_isometry hφiso hφcont hK htd hx₀ hY hxmem hymem
  exact ⟨γ, fun t => (hγ t).1⟩

end Work.Whitney.PathTools

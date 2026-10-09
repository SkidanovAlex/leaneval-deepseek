import Mathlib
import Submission.Work.SSGRoute.E1aClean.adicCompletion_near_one_isPow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000

namespace Work.SSGRoute.E1aClean

open IsDedekindDomain

/-- If `K` is a field and `F` a normed field, and the image of `φ : K →+* F` is dense in `F`,
then the image of the induced map `Kˣ →* Fˣ` is dense in the unit group `Fˣ` (with its
induced topology). -/
private theorem denseRange_unitsMap {K F : Type*} [Field K] [NormedField F]
    (φ : K →+* F) (hd : DenseRange φ) :
    DenseRange (Units.map φ.toMonoidHom) := by
  rw [DenseRange, dense_iff_inter_open]
  intro U hU hUne
  have hiff : IsOpen U ↔ ∃ t, IsOpen t ∧ Units.val ⁻¹' t = U :=
    (Units.isEmbedding_val₀.toIsInducing).isOpen_iff
  obtain ⟨W, hW, hWU⟩ := hiff.mp hU
  obtain ⟨u, hu⟩ := hUne
  have hWu : ((u : Fˣ) : F) ∈ W := by rw [← hWU] at hu; exact hu
  have hune : ((u : Fˣ) : F) ≠ 0 := u.ne_zero
  have hne : (W ∩ {x : F | x ≠ 0}).Nonempty := ⟨(u : F), hWu, hune⟩
  obtain ⟨y, hy⟩ :=
    (dense_iff_inter_open.mp hd) (W ∩ {x : F | x ≠ 0}) (hW.inter isOpen_ne) hne
  have hyW : y ∈ W := hy.1.1
  have hyne : y ≠ 0 := hy.1.2
  obtain ⟨k, hk_eq⟩ := hy.2
  have hk0 : k ≠ 0 := fun h0 => hyne (by rw [← hk_eq, h0, map_zero])
  refine ⟨Units.map φ.toMonoidHom (Units.mk0 k hk0), ?_, ?_⟩
  · rw [← hWU, Set.mem_preimage, Units.coe_map, Units.val_mk0]
    rw [show φ.toMonoidHom k = φ k from rfl, hk_eq]
    exact hyW
  · exact Set.mem_range.mpr ⟨Units.mk0 k hk0, rfl⟩

/-- An open subgroup containing a dense subset of a topological group is the whole group. -/
private theorem subgroup_eq_top_of_isOpen_of_dense {G : Type*} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] (H : Subgroup G) (hH : IsOpen (H : Set G))
    {s : Set G} (hs : s ⊆ (H : Set G)) (hd : Dense s) : H = ⊤ := by
  have hclosed : IsClosed (H : Set G) := H.isClosed_of_isOpen hH
  have hdenseH : Dense (H : Set G) := hd.mono hs
  have h1 : closure (H : Set G) = Set.univ := dense_iff_closure_eq.mp hdenseH
  have h2 : closure (H : Set G) = (H : Set G) := IsClosed.closure_eq hclosed
  rw [← Subgroup.coe_eq_univ, ← h2, h1]

/-- Abstract form of the main statement: if `φ : K →+* F` has dense image and every element of
`F` close enough to `1` is an `n`-th power, then every unit of `F` is the product of an element
of the image of `Kˣ` and an `n`-th power. The proof shows that the set of such products is an
open subgroup of `Fˣ` containing a ball around `1`, hence is open and closed, and it contains
the dense image of `Kˣ`. -/
private theorem units_eq_baseUnits_mul_pow_of_dense {K F : Type*} [Field K] [NormedField F]
    (φ : K →+* F) (hd : DenseRange φ) (n : ℕ)
    (hr : ∃ r : ℝ, 0 < r ∧ ∀ y : F, ‖y - 1‖ < r → ∃ w : Fˣ, ((w : F)) ^ n = y)
    (z : Fˣ) :
    ∃ k : Kˣ, ∃ w : Fˣ, Units.map φ.toMonoidHom k * w ^ n = z := by
  classical
  obtain ⟨r, hr_pos, hr⟩ := hr
  let ψ : Kˣ × Fˣ →* Fˣ :=
    { toFun := fun p => Units.map φ.toMonoidHom p.1 * p.2 ^ n
      map_one' := by simp
      map_mul' := by
        rintro ⟨k₁, w₁⟩ ⟨k₂, w₂⟩
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
        ac_rfl }
  let H : Subgroup Fˣ := ψ.range
  have hpow : ∀ w : Fˣ, w ^ n ∈ H := fun w => MonoidHom.mem_range.mpr ⟨(1, w), by simp [ψ]⟩
  have hbase : ∀ k : Kˣ, Units.map φ.toMonoidHom k ∈ H :=
    fun k => MonoidHom.mem_range.mpr ⟨(k, 1), by simp [ψ]⟩
  have hball : IsOpen {y : Fˣ | ‖((y : Fˣ) : F) - 1‖ < r} := by
    have hW : IsOpen {x : F | ‖x - 1‖ < r} := by
      apply isOpen_lt
      · exact continuous_norm.comp (continuous_id.sub continuous_const)
      · exact continuous_const
    exact hW.preimage Units.continuous_val
  have hball_sub : {y : Fˣ | ‖((y : Fˣ) : F) - 1‖ < r} ⊆ (H : Set Fˣ) := by
    intro y hy
    obtain ⟨w, hw⟩ := hr (y : F) hy
    have hyw : w ^ n = y := Units.ext (by rw [Units.val_pow_eq_pow_val, hw])
    rw [← hyw]
    exact hpow w
  have hH_nhds : (H : Set Fˣ) ∈ nhds (1 : Fˣ) := by
    refine Filter.mem_of_superset ?_ hball_sub
    refine hball.mem_nhds ?_
    simp only [Set.mem_ofPred_eq, Units.val_one, sub_self, norm_zero]
    exact hr_pos
  have hH_open : IsOpen (H : Set Fˣ) := H.isOpen_of_mem_nhds hH_nhds
  have hdense : DenseRange (Units.map φ.toMonoidHom) := denseRange_unitsMap φ hd
  have hrange : Set.range (Units.map φ.toMonoidHom) ⊆ (H : Set Fˣ) :=
    Set.range_subset_iff.mpr hbase
  have key : H = ⊤ := subgroup_eq_top_of_isOpen_of_dense H hH_open hrange hdense
  have hz : z ∈ H := key ▸ Subgroup.mem_top z
  obtain ⟨⟨k, w⟩, hkw⟩ := MonoidHom.mem_range.mp hz
  exact ⟨k, w, by simpa [ψ] using hkw⟩

theorem adicCompletion_units_eq_baseUnits_mul_pow {K : Type} [Field K] [NumberField K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (n : ℕ) (hn : 0 < n) (z : (q.adicCompletion K)ˣ) :
    ∃ (k : Kˣ) (w : (q.adicCompletion K)ˣ),
      Units.map (algebraMap K (q.adicCompletion K)).toMonoidHom k * w ^ n = z := by
  exact units_eq_baseUnits_mul_pow_of_dense
    (algebraMap K (q.adicCompletion K))
    (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K q) n
    (adicCompletion_near_one_isPow (K := K) q n hn) z

end Work.SSGRoute.E1aClean

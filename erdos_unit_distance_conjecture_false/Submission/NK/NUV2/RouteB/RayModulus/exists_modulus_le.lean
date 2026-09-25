import Mathlib
import Submission.NK.NUV2.RouteB.RayModulus.Defs
import Submission.Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one
import Submission.NK.NUV2.RouteB.RayModulus.real_pos_mem_closure_of_isOpen
import Submission.NK.NUV2.RouteB.RayModulus.complex_closure_of_isOpen_eq_top

open NumberField IsDedekindDomain
open scoped NumberField RestrictedProduct Topology

namespace NK.NUV2.RouteB.RayModulus

open NK.GlobalCFT

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K : Type} [Field K] [NumberField K]

abbrev AA (v : Place K) : Set ((Place.localField K v)ˣ) := (Place.localUnits K v : Set _)

lemma principalUnits_subset_of_isOpen (K : Type) [Field K] [NumberField K]
    (q : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (O : Set ((q.adicCompletion K)ˣ)) (hO : IsOpen O)
    (h1 : (1 : (q.adicCompletion K)ˣ) ∈ O) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ x : (q.adicCompletion K)ˣ,
      Valued.v ((x : q.adicCompletion K) - 1) ≤ WithZero.exp (-(m : ℤ)) → x ∈ O := by
  classical
  obtain ⟨π, hπval, -⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one (K := K) q
  have hOnhds : O ∈ 𝓝 (1 : (q.adicCompletion K)ˣ) := hO.mem_nhds h1
  rw [(Units.isEmbedding_val₀ (G₀ := q.adicCompletion K)).isInducing.nhds_eq_comap
    (1 : (q.adicCompletion K)ˣ)] at hOnhds
  obtain ⟨s, hs, hsub⟩ := Filter.mem_comap.mp hOnhds
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hs
  have hπnorm_lt : ‖(π : q.adicCompletion K)‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff, hπval]
    show WithZero.exp (-1 : ℤ) < (1 : WithZero (Multiplicative ℤ))
    rw [show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from rfl,
      WithZero.exp_lt_exp]
    norm_num
  have hπnorm_nonneg : (0 : ℝ) ≤ ‖(π : q.adicCompletion K)‖ := norm_nonneg _
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one hεpos hπnorm_lt
  refine ⟨max m₀ 1, le_max_right _ _, ?_⟩
  intro x hx
  apply hsub
  apply hεsub
  rw [Metric.mem_ball, dist_eq_norm]
  have hle : ‖(x : q.adicCompletion K) - 1‖ ≤ ‖((π : q.adicCompletion K) ^ max m₀ 1)‖ := by
    rw [Valued.toNormedField.norm_le_iff, map_pow]
    calc Valued.v ((x : q.adicCompletion K) - 1)
        ≤ WithZero.exp (-((max m₀ 1 : ℕ) : ℤ)) := hx
      _ = (WithZero.exp (-1 : ℤ)) ^ (max m₀ 1) := by
            rw [← WithZero.exp_nsmul, nsmul_eq_mul]; ring_nf
      _ = (Valued.v (π : q.adicCompletion K)) ^ (max m₀ 1) := by rw [hπval]
  rw [norm_pow] at hle
  exact lt_of_le_of_lt hle (lt_of_le_of_lt
    (pow_le_pow_of_le_one hπnorm_nonneg (le_of_lt hπnorm_lt) (le_max_left m₀ 1)) hm₀)

/-- The idèle which is `g` at the place `v` and `1` elsewhere. -/
def single (v : Place K) (g : (Place.localField K v)ˣ) : Idele K :=
  RestrictedProduct.mulSingle (G := fun v : Place K => (Place.localField K v)ˣ)
    (Place.localUnits K) v g

lemma single_self (v : Place K) (g : (Place.localField K v)ˣ) : single v g v = g := by
  show RestrictedProduct.mulSingle (G := fun v : Place K => (Place.localField K v)ˣ)
    (Place.localUnits K) v g v = g
  exact RestrictedProduct.mulSingle_eq_same (Place.localUnits K) v g

lemma single_of_ne {v w : Place K} (h : w ≠ v) (g : (Place.localField K v)ˣ) :
    single v g w = 1 := by
  show RestrictedProduct.mulSingle (G := fun v : Place K => (Place.localField K v)ˣ)
    (Place.localUnits K) v g w = 1
  exact RestrictedProduct.mulSingle_eq_of_ne (A := Place.localUnits K) (i := v) (j := w) g h

lemma single_mul (v : Place K) (a b : (Place.localField K v)ˣ) :
    single v (a * b) = single v a * single v b := by
  show RestrictedProduct.mulSingle (G := fun v : Place K => (Place.localField K v)ˣ)
      (Place.localUnits K) v (a * b) =
    RestrictedProduct.mulSingle (G := fun v : Place K => (Place.localField K v)ˣ)
      (Place.localUnits K) v a *
    RestrictedProduct.mulSingle (G := fun v : Place K => (Place.localField K v)ˣ)
      (Place.localUnits K) v b
  exact RestrictedProduct.mulSingle_mul (Place.localUnits K) v a b

lemma single_one (v : Place K) : single v (1 : (Place.localField K v)ˣ) = 1 := by
  show RestrictedProduct.mulSingle (G := fun v : Place K => (Place.localField K v)ˣ)
    (Place.localUnits K) v 1 = 1
  exact RestrictedProduct.mulSingle_one (Place.localUnits K) v

/-- The `single` map as a monoid homomorphism. -/
def singleHom (v : Place K) : (Place.localField K v)ˣ →* Idele K where
  toFun := single v
  map_one' := single_one v
  map_mul' := single_mul v

lemma singleHom_apply (v : Place K) (g : (Place.localField K v)ˣ) :
    singleHom v g = single v g := rfl

lemma exists_open_local_le (U : Subgroup (Idele K)) (hU : IsOpen (U : Set (Idele K))) :
    ∃ (I : Finset (Place K)) (O : ∀ v : Place K, Set ((Place.localField K v)ˣ)),
      (∀ v, v ∈ I → IsOpen (O v) ∧ (1 : (Place.localField K v)ˣ) ∈ O v ∧ O v ⊆ AA v) ∧
      (∀ x : Idele K, (∀ v, v ∉ (I : Set (Place K)) → x v ∈ AA v) →
          (∀ v, v ∈ (I : Set (Place K)) → x v ∈ O v) → x ∈ U) := by
  classical
  have hmem : (U : Set (Idele K)) ∈ 𝓝 (RestrictedProduct.structureMap
      (fun v : Place K => (Place.localField K v)ˣ) AA Filter.cofinite
      (1 : ∀ v, ↥(AA v))) := hU.mem_nhds U.one_mem
  rw [RestrictedProduct.nhds_eq_map_structureMap (R := fun v : Place K => (Place.localField K v)ˣ)
      (A := AA) (fun v => Place.isOpen_localUnits v) (1 : ∀ v, ↥(AA v))] at hmem
  have hW : RestrictedProduct.structureMap (fun v : Place K => (Place.localField K v)ˣ) AA
      Filter.cofinite ⁻¹' (U : Set (Idele K)) ∈ 𝓝 (1 : ∀ v, ↥(AA v)) := Filter.mem_map.mp hmem
  rw [nhds_pi] at hW
  obtain ⟨I, t, ht, htsub⟩ := Filter.mem_pi'.mp hW
  have hget : ∀ v : Place K, ∃ Ov : Set ((Place.localField K v)ˣ),
      IsOpen Ov ∧ (1 : (Place.localField K v)ˣ) ∈ Ov ∧ Ov ⊆ AA v ∧
      (∀ y : ↥(AA v), (y : (Place.localField K v)ˣ) ∈ Ov → y ∈ t v) := by
    intro v
    have hv : t v ∈ 𝓝 (1 : ↥(AA v)) := ht v
    obtain ⟨u, hu, hsub⟩ := (mem_nhds_subtype (AA v) (1 : ↥(AA v)) (t v)).mp hv
    obtain ⟨u', hu'sub, hu'open, hu'1⟩ := mem_nhds_iff.mp hu
    exact ⟨u' ∩ AA v, hu'open.inter (Place.isOpen_localUnits v),
      ⟨hu'1, Subgroup.one_mem _⟩, Set.inter_subset_right,
      fun y hy => hsub (hu'sub hy.1)⟩
  refine ⟨I, fun v => (hget v).choose, ?_, ?_⟩
  · intro v hv
    exact ⟨(hget v).choose_spec.1, (hget v).choose_spec.2.1, (hget v).choose_spec.2.2.1⟩
  · intro x hxout hxin
    let f : ∀ v, ↥(AA v) := fun v => if hv : v ∈ (I : Set (Place K))
        then ⟨x v, (hget v).choose_spec.2.2.1 (hxin v hv)⟩
        else ⟨x v, hxout v hv⟩
    have hfv : ∀ v, (f v : (Place.localField K v)ˣ) = x v := by
      intro v
      by_cases hv : v ∈ (I : Set (Place K))
      · dsimp only [f]
        rw [dif_pos hv]
      · dsimp only [f]
        rw [dif_neg hv]
    have hfmem : f ∈ Set.pi (↑I) t := by
      intro v hv
      refine (hget v).choose_spec.2.2.2 (f v) ?_
      rw [hfv v]
      exact hxin v hv
    have h2 : RestrictedProduct.structureMap (fun v : Place K => (Place.localField K v)ˣ) AA
        Filter.cofinite f ∈ (U : Set (Idele K)) := Set.mem_preimage.mp (htsub hfmem)
    have hfx : RestrictedProduct.structureMap (fun v : Place K => (Place.localField K v)ˣ) AA
        Filter.cofinite f = x := by
      apply Subtype.ext
      funext v
      exact hfv v
    rwa [hfx] at h2

theorem exists_modulus_le (K : Type) [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K)) (hU : IsOpen (U : Set (NK.GlobalCFT.Idele K))) :
    ∃ 𝔪 : NK.NUV2.RouteB.Modulus K, NK.NUV2.RouteB.CongSubgroup K 𝔪 ≤ U := by
  classical
  obtain ⟨I, O, hO, hWU⟩ := exists_open_local_le U hU
  have hex : ∀ q : HeightOneSpectrum (RingOfIntegers K), Place.ofFinite q ∈ (I : Set (Place K)) →
      ∃ m : ℕ, 1 ≤ m ∧ ∀ x : (q.adicCompletion K)ˣ,
        Valued.v ((x : q.adicCompletion K) - 1) ≤ WithZero.exp (-(m : ℤ)) →
          x ∈ O (Place.ofFinite q) :=
    fun q hq => principalUnits_subset_of_isOpen K q (O (Place.ofFinite q)) (hO _ hq).1 (hO _ hq).2.1
  have hfs : HasFiniteSupport K
      (fun q : HeightOneSpectrum (RingOfIntegers K) =>
        if h : Place.ofFinite q ∈ (I : Set (Place K)) then (hex q h).choose else 0) := by
    rw [HasFiniteSupport, Filter.eventually_cofinite]
    have hfin : ({q : HeightOneSpectrum (RingOfIntegers K) |
        Place.ofFinite q ∈ (I : Set (Place K))}).Finite :=
      Set.Finite.preimage (f := Place.ofFinite) (fun a _ b _ h => Place.ofFinite_inj.mp h)
        I.finite_toSet
    refine hfin.subset ?_
    intro q hq
    by_contra h
    exact hq (dif_neg h)
  let 𝔪 : Modulus K :=
    { exps := fun q => if h : Place.ofFinite q ∈ (I : Set (Place K)) then (hex q h).choose else 0
      finite_support := hfs
      pos := {w : InfinitePlace K | Place.ofInfinite w ∈ (I : Set (Place K))} }
  have hexps_pos : ∀ q (h : Place.ofFinite q ∈ (I : Set (Place K))),
      𝔪.exps q = (hex q h).choose := fun q h => dif_pos h
  refine ⟨𝔪, ?_⟩
  intro x hx
  rw [Modulus.mem_congSubgroup_iff] at hx
  obtain ⟨hxfin, hxinf⟩ := hx
  have hxloc : ∀ v : Place K, x v ∈ AA v := by
    intro v
    rcases v with w | q
    · exact Subgroup.mem_top _
    · show x (Place.ofFinite q) ∈ Place.localUnits K (Place.ofFinite q)
      rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one]
      exact (hxfin q).1
  have hxv : ∀ v, v ∈ (I : Set (Place K)) → x v ∈ Subgroup.closure (O v) := by
    intro v hv
    rcases v with w | q
    · by_cases hwr : w.IsReal
      · have hpos : w ∈ 𝔪.pos := hv
        exact real_pos_mem_closure_of_isOpen K w hwr (O (Place.ofInfinite w)) (hO _ hv).1
          (hO _ hv).2.1 _ (hxinf w hwr hpos)
      · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hwr
        rw [complex_closure_of_isOpen_eq_top K w hc (O (Place.ofInfinite w)) (hO _ hv).1
          (hO _ hv).2.1]
        exact Subgroup.mem_top _
    · have hc := (hxfin q).2
      rw [IsCongAt] at hc
      rw [hexps_pos q hv] at hc
      exact Subgroup.subset_closure ((hex q hv).choose_spec.2 _ hc)
  let z : Idele K := RestrictedProduct.mk
    (fun v : Place K => if v ∈ (I : Set (Place K)) then 1 else x v)
    (by
      filter_upwards [x.2] with v hv
      by_cases h : v ∈ (I : Set (Place K))
      · rw [if_pos h]; exact Subgroup.one_mem _
      · rw [if_neg h]; exact hv)
  have hzv : ∀ v, z v = if v ∈ (I : Set (Place K)) then 1 else x v := fun v => rfl
  have hzU : z ∈ U := by
    refine hWU z (fun v hv => ?_) (fun v hv => ?_)
    · rw [hzv v, if_neg hv]; exact hxloc v
    · rw [hzv v, if_pos hv]; exact (hO v hv).2.1
  have hmulU : ∀ v ∈ I, single v (x v) ∈ U := by
    intro v hv
    have hle : Subgroup.closure (O v) ≤ Subgroup.comap (singleHom v) U := by
      rw [Subgroup.closure_le]
      intro o ho
      refine hWU (singleHom v o) (fun w hw => ?_) (fun w hw => ?_)
      · rw [singleHom_apply, single_of_ne (v := v) (w := w) (fun h : w = v => hw (h ▸ hv)) o]
        exact Subgroup.one_mem _
      · rw [singleHom_apply]
        by_cases hwv : w = v
        · subst hwv
          rw [single_self]
          exact ho
        · rw [single_of_ne (v := v) (w := w) hwv o]
          exact (hO w hw).2.1
    exact Subgroup.mem_comap.mp (hle (hxv v hv))
  have hprodU : (∏ v ∈ I, single v (x v)) ∈ U := Subgroup.prod_mem U hmulU
  have hdecomp : x = z * ∏ v ∈ I, single v (x v) := by
    apply Idele.ext
    intro w
    rw [Idele.mul_apply, hzv w]
    have hprod : (∏ v ∈ I, single v (x v) : Idele K) w =
        ∏ v ∈ I, single v (x v) w := by
      rw [← Idele.eval_apply w (∏ v ∈ I, single v (x v)), map_prod]
      rfl
    rw [hprod]
    by_cases hw : w ∈ (I : Set (Place K))
    · rw [if_pos hw]
      rw [Finset.prod_eq_single w
        (fun b _ hbw => by
          rw [single_of_ne (v := b) (w := w) hbw.symm (x b)])
        (fun hw' => absurd (Finset.mem_coe.mp hw) hw')]
      rw [single_self, one_mul]
    · rw [if_neg hw]
      have h1 : ∏ v ∈ I, single v (x v) w = 1 := by
        apply Finset.prod_eq_one
        intro b hb
        rw [single_of_ne (v := b) (w := w)
          (fun h : w = b => hw (h ▸ (Finset.mem_coe.mpr hb))) (x b)]
      rw [h1, mul_one]
  rw [hdecomp]
  exact Subgroup.mul_mem _ hzU hprodU

end

end NK.NUV2.RouteB.RayModulus

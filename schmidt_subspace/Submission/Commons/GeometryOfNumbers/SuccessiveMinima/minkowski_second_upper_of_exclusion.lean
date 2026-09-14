import Mathlib
import Submission.Commons.GeometryOfNumbers.SuccessiveMinima.gauge_realizers_exclusion
import Submission.Commons.GeometryOfNumbers.SuccessiveMinima.exists_unimodular_flag
import Submission.Commons.GeometryOfNumbers.SuccessiveMinima.successive_minima_unimodular
import Submission.Commons.GeometryOfNumbers.SuccessiveMinima.measure_preserving_fin_succ_split
import Submission.Commons.GeometryOfNumbers.SuccessiveMinima.volume_biUnion_translates_interior
import Submission.Commons.GeometryOfNumbers.SuccessiveMinima.measure_preserving_fin_split
import Submission.Commons.Algebra.BigOperators.prod_flag_ite
import Submission.Commons.Algebra.BigOperators.prod_ratio_pow_telescope

open MeasureTheory Set Filter
open scoped Pointwise BigOperators Topology

namespace Commons.GeometryOfNumbers.SuccessiveMinima

open Commons.Algebra.BigOperators

noncomputable def lam (N : ℕ) (K : Set (Fin N → ℝ)) (ℓ : ℕ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ ∃ v : Fin ℓ → (Fin N → ℤ),
    LinearIndependent ℝ (fun a => fun k => (v a k : ℝ)) ∧
    ∀ a, (fun k => (v a k : ℝ)) ∈ t • K}

lemma lam_def (N : ℕ) (K : Set (Fin N → ℝ)) (ℓ : ℕ) :
    lam N K ℓ = sInf {t : ℝ | 0 < t ∧ ∃ v : Fin ℓ → (Fin N → ℤ),
      LinearIndependent ℝ (fun a => fun k => (v a k : ℝ)) ∧
      ∀ a, (fun k => (v a k : ℝ)) ∈ t • K} := rfl

lemma bddBelow_lam_set (N : ℕ) (K : Set (Fin N → ℝ)) (ℓ : ℕ) :
    BddBelow {t : ℝ | 0 < t ∧ ∃ v : Fin ℓ → (Fin N → ℤ),
      LinearIndependent ℝ (fun a => fun k => (v a k : ℝ)) ∧
      ∀ a, (fun k => (v a k : ℝ)) ∈ t • K} :=
  ⟨0, fun _ ht => ht.1.le⟩

lemma lam_nonneg (N : ℕ) (K : Set (Fin N → ℝ)) (ℓ : ℕ) : 0 ≤ lam N K ℓ :=
  Real.sInf_nonneg (fun _ ht => ht.1.le)

lemma lam_le_of_contains (N : ℕ) (K : Set (Fin N → ℝ)) (ℓ : ℕ) {t : ℝ} (ht : 0 < t)
    (v : Fin ℓ → (Fin N → ℤ))
    (hv : LinearIndependent ℝ (fun a => fun k => (v a k : ℝ)))
    (hvt : ∀ a, (fun k => (v a k : ℝ)) ∈ t • K) :
    lam N K ℓ ≤ t :=
  csInf_le (bddBelow_lam_set N K ℓ) ⟨ht, v, hv, hvt⟩

/-- Coordinate bounds for a bounded set: there is `R ≥ 0` with `|x k| ≤ R` for all `x ∈ K`. -/
lemma exists_coord_bound (N : ℕ) {K : Set (Fin N → ℝ)} (hbdd : Bornology.IsBounded K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ K, ∀ k : Fin N, |x k| ≤ R := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin N → ℝ)).mp hbdd
  refine ⟨max R 0, le_max_right _ _, fun x hx k => ?_⟩
  have h1 : ‖x‖ ≤ R := by
    have := hR hx
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
  exact le_trans (norm_le_pi_norm x k) (le_trans h1 (le_max_left _ _))

/-- The standard basis vector of `ℝ^N` has sup-norm `1`. -/
lemma norm_pi_single_one (N : ℕ) (k : Fin N) : ‖(Pi.single k (1:ℝ) : Fin N → ℝ)‖ = 1 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
    intro i
    by_cases h : i = k
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  · have := norm_le_pi_norm (Pi.single k (1:ℝ) : Fin N → ℝ) k
    simpa using this

/-- The standard basis vectors are linearly independent. -/
lemma linearIndependent_pi_single_one (N : ℕ) :
    LinearIndependent ℝ (fun k : Fin N => (Pi.single k (1 : ℝ) : Fin N → ℝ)) := by
  convert (Pi.basisFun ℝ (Fin N)).linearIndependent using 2
  rw [Pi.basisFun_apply]

/-- The family of the first `ℓ` standard basis vectors, as integer vectors. -/
noncomputable def stdVec (N ℓ : ℕ) (h : ℓ ≤ N) (a : Fin ℓ) : Fin N → ℤ :=
  Pi.single (Fin.castLE h a) 1

lemma stdVec_cast (N ℓ : ℕ) (h : ℓ ≤ N) (a : Fin ℓ) :
    (fun k => ((stdVec N ℓ h a : Fin N → ℤ) k : ℝ)) =
      (Pi.single (Fin.castLE h a) (1 : ℝ) : Fin N → ℝ) := by
  ext k
  by_cases hk : k = Fin.castLE h a
  · subst hk
    simp [stdVec, Pi.single_eq_same]
  · simp [stdVec, Pi.single_eq_of_ne hk]

lemma stdVec_linearIndependent (N ℓ : ℕ) (h : ℓ ≤ N) :
    LinearIndependent ℝ (fun a : Fin ℓ => (fun k => (stdVec N ℓ h a k : ℝ))) := by
  have hb := linearIndependent_pi_single_one N
  have hcomp := hb.comp (Fin.castLE h) (Fin.castLE_injective h)
  convert hcomp using 2
  exact stdVec_cast N ℓ h _

lemma stdVec_mem (N ℓ : ℕ) (h : ℓ ≤ N) (K : Set (Fin N → ℝ)) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : Fin N → ℝ) r ⊆ K) (a : Fin ℓ) :
    (fun k => (stdVec N ℓ h a k : ℝ)) ∈ (2 / r) • K := by
  have h2r : (0 : ℝ) < 2 / r := by positivity
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt h2r)]
  apply hball
  rw [Metric.mem_ball, dist_eq_norm, sub_zero, stdVec_cast N ℓ h a, norm_smul,
    norm_pi_single_one, mul_one, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (2/r)⁻¹),
    inv_div]
  linarith

lemma lam_set_nonempty_of_mem_interior (N : ℕ) (K : Set (Fin N → ℝ)) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : Fin N → ℝ) r ⊆ K) (ℓ : ℕ) (hℓ : ℓ ≤ N) :
    ({t : ℝ | 0 < t ∧ ∃ v : Fin ℓ → (Fin N → ℤ),
      LinearIndependent ℝ (fun a => fun k => (v a k : ℝ)) ∧
      ∀ a, (fun k => (v a k : ℝ)) ∈ t • K}).Nonempty :=
  ⟨2 / r, by positivity, stdVec N ℓ hℓ, stdVec_linearIndependent N ℓ hℓ,
    fun a => stdVec_mem N ℓ hℓ K hr hball a⟩

lemma lam_le_of_mem_interior (N : ℕ) (K : Set (Fin N → ℝ)) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : Fin N → ℝ) r ⊆ K) (ℓ : ℕ) (hℓ : ℓ ≤ N) :
    lam N K ℓ ≤ 2 / r :=
  lam_le_of_contains N K ℓ (by positivity) (stdVec N ℓ hℓ)
    (stdVec_linearIndependent N ℓ hℓ) (fun a => stdVec_mem N ℓ hℓ K hr hball a)

/-- Monotonicity of the successive minima in the index. -/
lemma lam_mono (N : ℕ) (K : Set (Fin N → ℝ)) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : Fin N → ℝ) r ⊆ K) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) :
    lam N K i ≤ lam N K j := by
  rw [lam_def, lam_def]
  refine le_csInf (lam_set_nonempty_of_mem_interior N K hr hball j hj) ?_
  rintro t ⟨ht, v, hv, hvt⟩
  exact lam_le_of_contains N K i ht (fun a : Fin i => v (Fin.castLE hij a))
    (hv.comp _ (Fin.castLE_injective hij)) (fun a => hvt _)

/-- Positivity of the successive minima for `1 ≤ ℓ ≤ N` when `K` has nonempty interior. -/
lemma lam_pos (N : ℕ) (K : Set (Fin N → ℝ)) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : Fin N → ℝ) r ⊆ K) (hbdd : Bornology.IsBounded K)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hℓN : ℓ ≤ N) : 0 < lam N K ℓ := by
  obtain ⟨R, _hR0, hR⟩ := exists_coord_bound N hbdd
  have hRpos : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine lt_of_lt_of_le (div_pos one_pos hRpos) ?_
  rw [lam_def]
  refine le_csInf (lam_set_nonempty_of_mem_interior N K hr hball ℓ hℓN) ?_
  rintro t ⟨ht, v, hv, hvt⟩
  haveI : Nonempty (Fin ℓ) := ⟨⟨0, hℓ⟩⟩
  set a₀ : Fin ℓ := Classical.arbitrary (Fin ℓ) with ha₀
  have hne : (fun k => (v a₀ k : ℝ)) ≠ 0 := hv.ne_zero a₀
  obtain ⟨k, hk⟩ : ∃ k : Fin N, v a₀ k ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (funext fun k => by simpa using hc k)
  have hmem : |((v a₀ k : ℤ) : ℝ)| ≤ t * max R 1 := by
    have hthis := hvt a₀
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt ht)] at hthis
    have hb := hR (t⁻¹ • (fun k => (v a₀ k : ℝ))) hthis k
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr ht),
      inv_mul_le_iff₀ ht] at hb
    exact le_trans hb (by nlinarith [le_max_left R 1])
  have hge : (1 : ℝ) ≤ |((v a₀ k : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |v a₀ k| := Int.one_le_abs hk
    exact_mod_cast this
  rw [div_le_iff₀ hRpos]
  exact le_trans hge hmem

/-- **`lam N K 1` is at most the gauge of any nonzero integer vector.** -/
lemma lam_one_le_gauge (N : ℕ) (K : Set (Fin N → ℝ)) (habs : Absorbent ℝ K)
    {y : Fin N → ℤ} (hy : y ≠ 0) :
    lam N K 1 ≤ gauge K (fun k => (y k : ℝ)) := by
  set g := gauge K (fun k => (y k : ℝ)) with hg
  have hmem : (fun k => (y k : ℝ)) ≠ 0 := by
    intro h
    exact hy (funext fun k => by
      have := congrFun h k
      simpa using this)
  have hLI : LinearIndependent ℝ (fun _ : Fin 1 => (fun k => (y k : ℝ))) := by
    rw [linearIndependent_unique_iff]
    exact hmem
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨t, ht0, htg, htmem⟩ := exists_lt_of_gauge_lt habs
    (x := fun k => (y k : ℝ)) (a := g + ε) (by linarith)
  have hle : lam N K 1 ≤ t := lam_le_of_contains N K 1 ht0 (fun _ => y) hLI (fun _ => htmem)
  linarith


/-! ### The box of lattice points, its flag part and its transversal part

These are the combinatorial objects of the proof of Minkowski's second theorem (Henk,
arXiv:math/0204158, last section): the box `boxVec N q` of the lattice points in `[-q,q]^N`,
its "flag" part `flagVec N q i` (supported in the first `i` coordinates) and its "transversal"
part `transvVec N q i` (supported in the last `N - i` coordinates), together with the
decomposition `boxVec = transvVec + flagVec`. -/

/-- Encoding of a `Fin (2q+1)`-tuple as a lattice vector in `[-q,q]^N`. -/
noncomputable def boxEnc (N q : ℕ) (f : Fin N → Fin (2*q+1)) : Fin N → ℝ :=
  fun k => (((f k : ℤ) - (q:ℤ) : ℤ) : ℝ)

lemma boxEnc_injOn (N q : ℕ) : Set.InjOn (boxEnc N q) Set.univ := by
  intro f _ g _ h
  funext k
  have hk : boxEnc N q f k = boxEnc N q g k := congrFun h k
  have hk' : ((f k : ℤ) : ℝ) = ((g k : ℤ) : ℝ) := by
    have h1 : (((f k : ℤ) : ℝ) - (q:ℝ)) = (((g k : ℤ) : ℝ) - (q:ℝ)) := by
      simpa [boxEnc] using hk
    linarith
  have hk'' : (f k : ℤ) = (g k : ℤ) := by exact_mod_cast hk'
  exact Fin.ext (by omega)

/-- The box of lattice points with all coordinates in `[-q,q]`, as a finite set of vectors. -/
noncomputable def boxVec (N q : ℕ) : Finset (Fin N → ℝ) :=
  (Finset.univ : Finset (Fin N → Fin (2*q+1))).image (boxEnc N q)

lemma mem_boxVec_iff (N q : ℕ) (z : Fin N → ℝ) :
    z ∈ boxVec N q ↔ ∃ f : Fin N → Fin (2*q+1), boxEnc N q f = z := by
  simp [boxVec]

lemma card_boxVec (N q : ℕ) : (boxVec N q).card = (2*q+1)^N := by
  rw [boxVec, Finset.card_image_of_injOn (s := Finset.univ) (by simpa using boxEnc_injOn N q),
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

lemma mem_boxVec (N q : ℕ) (z : Fin N → ℝ) :
    z ∈ boxVec N q ↔ ∃ w : Fin N → ℤ, (∀ k, |w k| ≤ (q:ℤ)) ∧ z = fun k => (w k : ℝ) := by
  constructor
  · intro hz
    rw [mem_boxVec_iff] at hz
    obtain ⟨f, rfl⟩ := hz
    refine ⟨fun k => (f k : ℤ) - q, ?_, ?_⟩
    · intro k
      show |(f k : ℤ) - (q:ℤ)| ≤ (q:ℤ)
      have h1 : (0:ℤ) ≤ (f k : ℤ) := Int.natCast_nonneg _
      have h2 : (f k : ℤ) ≤ 2*q := by have := (f k).isLt; omega
      rw [abs_le]; omega
    · rfl
  · rintro ⟨w, hw, rfl⟩
    rw [mem_boxVec_iff]
    refine ⟨fun k => ⟨(w k + q).toNat, ?_⟩, ?_⟩
    · have := hw k; rw [abs_le] at this; omega
    · funext k
      simp only [boxEnc]
      have h := hw k; rw [abs_le] at h
      have hcast : (((w k + q).toNat : ℤ)) = w k + q := by omega
      rw [hcast]
      push_cast
      ring

/-- The flag part: elements of the box supported in the first `i` coordinates. -/
noncomputable def flagVec (N q i : ℕ) : Finset (Fin N → ℝ) :=
  (boxVec N q).filter (fun z => ∀ k : Fin N, i ≤ k.val → z k = 0)

/-- The transversal part: elements of the box supported in the last `N - i` coordinates. -/
noncomputable def transvVec (N q i : ℕ) : Finset (Fin N → ℝ) :=
  (boxVec N q).filter (fun z => ∀ k : Fin N, k.val < i → z k = 0)

lemma mem_flagVec (N q i : ℕ) (z : Fin N → ℝ) :
    z ∈ flagVec N q i ↔ z ∈ boxVec N q ∧ ∀ k : Fin N, i ≤ k.val → z k = 0 := by
  simp [flagVec]

lemma mem_transvVec (N q i : ℕ) (z : Fin N → ℝ) :
    z ∈ transvVec N q i ↔ z ∈ boxVec N q ∧ ∀ k : Fin N, k.val < i → z k = 0 := by
  simp [transvVec]

/-- The transversal component of a vector: the coordinates `≥ i`. -/
noncomputable def transvPart (N i : ℕ) (z : Fin N → ℝ) : Fin N → ℝ :=
  fun k => if k.val < i then 0 else z k

/-- The flag component of a vector: the coordinates `< i`. -/
noncomputable def flagPart (N i : ℕ) (z : Fin N → ℝ) : Fin N → ℝ :=
  fun k => if k.val < i then z k else 0

lemma transvPart_add_flagPart (N i : ℕ) (z : Fin N → ℝ) :
    transvPart N i z + flagPart N i z = z := by
  funext k
  simp only [transvPart, flagPart, Pi.add_apply]
  by_cases h : k.val < i <;> simp [h]

lemma transvPart_mem (N q i : ℕ) {z : Fin N → ℝ} {w : Fin N → ℤ}
    (hw : ∀ k, |w k| ≤ (q:ℤ)) (hz : z = fun k => (w k : ℝ)) :
    transvPart N i z ∈ boxVec N q := by
  refine (mem_boxVec N q _).mpr ⟨fun k => if k.val < i then 0 else w k, ?_, ?_⟩
  · intro k
    by_cases h : k.val < i
    · simp [h]
    · simp only [if_neg h]
      exact hw k
  · funext k
    have hzk : z k = (w k : ℝ) := by rw [hz]
    simp only [transvPart, hzk]
    by_cases h : k.val < i <;> simp [h]

lemma flagPart_mem (N q i : ℕ) {z : Fin N → ℝ} {w : Fin N → ℤ}
    (hw : ∀ k, |w k| ≤ (q:ℤ)) (hz : z = fun k => (w k : ℝ)) :
    flagPart N i z ∈ boxVec N q := by
  refine (mem_boxVec N q _).mpr ⟨fun k => if k.val < i then w k else 0, ?_, ?_⟩
  · intro k
    by_cases h : k.val < i
    · simp only [if_pos h]; exact hw k
    · simp [h]
  · funext k
    have hzk : z k = (w k : ℝ) := by rw [hz]
    simp only [flagPart, hzk]
    by_cases h : k.val < i <;> simp [h]

lemma transvPart_mem_transvVec (N q i : ℕ) {z : Fin N → ℝ} {w : Fin N → ℤ}
    (hw : ∀ k, |w k| ≤ (q:ℤ)) (hz : z = fun k => (w k : ℝ)) :
    transvPart N i z ∈ transvVec N q i := by
  rw [mem_transvVec]
  refine ⟨transvPart_mem N q i hw hz, ?_⟩
  intro k hk
  simp only [transvPart, if_pos hk]

lemma flagPart_mem_flagVec (N q i : ℕ) {z : Fin N → ℝ} {w : Fin N → ℤ}
    (hw : ∀ k, |w k| ≤ (q:ℤ)) (hz : z = fun k => (w k : ℝ)) :
    flagPart N i z ∈ flagVec N q i := by
  rw [mem_flagVec]
  refine ⟨flagPart_mem N q i hw hz, ?_⟩
  intro k hk
  simp only [flagPart, if_neg (not_lt.mpr hk)]

lemma boxVec_decomp (N q i : ℕ) {z : Fin N → ℝ} (hz : z ∈ boxVec N q) :
    ∃ t ∈ transvVec N q i, ∃ p ∈ flagVec N q i, z = t + p := by
  obtain ⟨w, hw, hz'⟩ := (mem_boxVec N q z).mp hz
  refine ⟨transvPart N i z, transvPart_mem_transvVec N q i hw hz', flagPart N i z,
    flagPart_mem_flagVec N q i hw hz', ?_⟩
  exact (transvPart_add_flagPart N i z).symm

lemma boxVec_prod_mem (N q i : ℕ) {t p : Fin N → ℝ} (ht : t ∈ transvVec N q i)
    (hp : p ∈ flagVec N q i) : t + p ∈ boxVec N q := by
  rw [mem_transvVec] at ht
  rw [mem_flagVec] at hp
  obtain ⟨wt, hwt, htw⟩ := (mem_boxVec N q t).mp ht.1
  obtain ⟨wp, hwp, hpw⟩ := (mem_boxVec N q p).mp hp.1
  refine (mem_boxVec N q (t + p)).mpr ⟨fun k => wt k + wp k, ?_, ?_⟩
  · intro k
    have htwk : t k = (wt k : ℝ) := congrFun htw k
    have hpwk : p k = (wp k : ℝ) := congrFun hpw k
    show |wt k + wp k| ≤ (q : ℤ)
    by_cases hk : k.val < i
    · have hwt0 : wt k = 0 := by
        have h1 : (wt k : ℝ) = 0 := by rw [← htwk, ht.2 k hk]
        exact_mod_cast h1
      rw [hwt0, zero_add]; exact hwp k
    · have hki : i ≤ k.val := not_lt.mp hk
      have hwp0 : wp k = 0 := by
        have h1 : (wp k : ℝ) = 0 := by rw [← hpwk, hp.2 k hki]
        exact_mod_cast h1
      rw [hwp0, add_zero]; exact hwt k
  · funext k
    simp only [Pi.add_apply]
    rw [htw, hpw]
    push_cast
    ring


/-! ## The two remaining statements: the "flag theorem" and the target

`minkowski_second_upper_flag` is the straightened form of Minkowski's second theorem: the body
satisfies the *strong* interior-exclusion property with respect to the standard coordinate flag
(`gauge K y < lam N K ℓ` forces the coordinates `≥ ℓ - 1` of `y` to vanish).  The target theorem
`minkowski_second_upper_of_exclusion` follows from it by straightening with the unimodular map
supplied by `Commons.GeometryOfNumbers.SuccessiveMinima.exists_unimodular_flag` applied to the
realizers of `Commons.GeometryOfNumbers.SuccessiveMinima.gauge_realizers_exclusion`; the
invariance of the successive minima and the volume is
`Commons.GeometryOfNumbers.SuccessiveMinima.successive_minima_unimodular`. -/


variable {N : ℕ} {K : Set (Fin N → ℝ)}

/-- `0` lies in the interior of a symmetric convex body with nonempty interior. -/
lemma zero_mem_interior_of_convex_symm (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K)
    (hint : (interior K).Nonempty) : (0 : Fin N → ℝ) ∈ interior K := by
  obtain ⟨x, hx⟩ := hint
  have h := hconv.combo_interior_self_mem_interior hx (hsym x (interior_subset hx))
    (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  simpa using h

lemma exists_ball_subset (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K)
    (hint : (interior K).Nonempty) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : Fin N → ℝ) r ⊆ K := by
  have h0 := zero_mem_interior_of_convex_symm hconv hsym hint
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  exact ⟨r, hr, hball⟩

lemma balanced_of_convex_symm (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K) : Balanced ℝ K :=
  (balanced_iff_neg_mem hconv).mpr (fun x hx => hsym x hx)

lemma absorbent_of_convex_symm (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K)
    (hint : (interior K).Nonempty) : Absorbent ℝ K :=
  absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp (zero_mem_interior_of_convex_symm hconv hsym hint))

/-- The dilated body `(λ_j / 2) • K` of the proof of Minkowski's second theorem. -/
noncomputable def Dil (N : ℕ) (K : Set (Fin N → ℝ)) (j : ℕ) : Set (Fin N → ℝ) :=
  (lam N K j / 2) • K

/-- Points of the interior of `Dil j = (λ_j/2) • K` have gauge `< λ_j / 2`. -/
lemma gauge_lt_half_of_mem_interior_Dil (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K)
    {j : ℕ} (hjpos : 0 < lam N K j) {y : Fin N → ℝ}
    (hy : y ∈ interior (Dil N K j)) : gauge K y < lam N K j / 2 := by
  have hlamne : lam N K j / 2 ≠ 0 := by positivity
  rw [Dil, interior_smul₀ hlamne] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  have hgw : gauge K w < 1 := interior_subset_gauge_lt_one K hw
  have hbal : Balanced ℝ K := balanced_of_convex_symm hconv hsym
  rw [gauge_smul hbal]
  have hnorm : ‖lam N K j / 2‖ = lam N K j / 2 := Real.norm_of_nonneg (by linarith)
  rw [hnorm]
  calc lam N K j / 2 * gauge K w < lam N K j / 2 * 1 :=
        mul_lt_mul_of_pos_left hgw (by linarith)
    _ = lam N K j / 2 := by ring

/-- Scaling a set multiplies its Lebesgue measure by `|r|^N`. -/
lemma volume_real_smul (r : ℝ) (s : Set (Fin N → ℝ)) :
    volume.real (r • s) = |r|^N * volume.real s := by
  rw [Measure.real_def, Measure.addHaar_smul, Measure.real_def, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), Module.finrank_fin_fun, abs_pow]

/-- For a closed convex set the interior has the same Lebesgue measure as the set itself. -/
lemma volume_interior_eq_volume (hconv : Convex ℝ K) (hclosed : IsClosed K) :
    volume (interior K) = volume K := by
  have hfr : volume (frontier K) = 0 := Convex.addHaar_frontier volume hconv
  have hsub : K \ interior K ⊆ frontier K := by
    intro x hx
    exact ⟨subset_closure hx.1, hx.2⟩
  have hsub_null : volume (K \ interior K) = 0 :=
    le_antisymm (le_trans (measure_mono hsub) (le_of_eq hfr)) (by simp)
  have hnull : volume (K \ interior K) = 0 :=
    hsub_null
  have hK : K = interior K ∪ (K \ interior K) := (Set.union_sdiff_cancel interior_subset).symm
  refine le_antisymm (measure_mono interior_subset) ?_
  calc volume K = volume (interior K ∪ (K \ interior K)) := by
        conv_lhs => rw [hK]
    _ ≤ volume (interior K) + volume (K \ interior K) := measure_union_le _ _
    _ = volume (interior K) := by rw [hnull, add_zero]

/-- Volume of the interior of `Dil j`, in terms of `λ_j` and the volume of `K`. -/
lemma volume_real_interior_Dil (hconv : Convex ℝ K) (hclosed : IsClosed K)
    (hsym : ∀ x ∈ K, -x ∈ K) {j : ℕ} (hjpos : 0 < lam N K j) :
    volume.real (interior (Dil N K j)) = (lam N K j / 2)^N * (volume K).toReal := by
  have hlamne : lam N K j / 2 ≠ 0 := by positivity
  have h1 : interior (Dil N K j) = (lam N K j / 2) • interior K := by
    rw [Dil, interior_smul₀ hlamne]
  have h2 : volume.real (interior K) = (volume K).toReal := by
    rw [Measure.real_def, volume_interior_eq_volume hconv hclosed]
  rw [h1, volume_real_smul, abs_of_nonneg (by linarith : (0:ℝ) ≤ lam N K j / 2), h2]




variable {N : ℕ} {K : Set (Fin N → ℝ)}

/-- A lattice vector, viewed as a real vector. -/
def cZ {M : ℕ} (v : Fin M → ℤ) : Fin M → ℝ := fun k => (v k : ℝ)

lemma cZ_sub {M : ℕ} (v w : Fin M → ℤ) : cZ (v - w) = cZ v - cZ w := by
  funext k; simp [cZ]

lemma cZ_ne_zero {M : ℕ} {v : Fin M → ℤ} (h : cZ v ≠ 0) : v ≠ 0 := by
  intro hv; exact h (by rw [hv]; funext k; simp [cZ])

lemma zsmul_helper (n : ℕ) (c : ℝ) : (n : ℕ) • c = ((n : ℤ) : ℝ) * c := by
  rw [nsmul_eq_mul]; norm_num

/-- The successive minima are positive (for `1 ≤ j ≤ N`) when the body has nonempty interior. -/
lemma lam_pos_of (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K)
    (hbdd : Bornology.IsBounded K) (hint : (interior K).Nonempty)
    {j : ℕ} (hj1 : 1 ≤ j) (hjN : j ≤ N) : 0 < lam N K j := by
  obtain ⟨r, hr, hball⟩ := exists_ball_subset hconv hsym hint
  exact lam_pos N K hr hball hbdd hj1 hjN

lemma volume_lt_top_of_bdd {S : Set (Fin N → ℝ)} (h : Bornology.IsBounded S) : volume S < ⊤ :=
  h.measure_lt_top

/-- **Disjointness of the translates of the interior of `Dil j` by lattice points that differ
outside the first `j - 1` coordinates.**  This is Henk's eq. (cut) in straightened form: the
strong exclusion property at level `j` says that a lattice point whose gauge is `< λ_j` lies in
the span of the first `j - 1` coordinate vectors. -/
lemma disjoint_translates_interior_Dil {j : ℕ} (hj1 : 1 ≤ j) (hjN : j ≤ N)
    (hjpos : 0 < lam N K j)
    (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty)
    (hexcl : ∀ (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓN : ℓ ≤ N) (y : Fin N → ℤ),
      gauge K (cZ y) < lam N K ℓ → ∀ j : Fin N, ℓ - 1 ≤ j.val → y j = 0)
    {z z' : Fin N → ℤ} (hne : ∃ k : Fin N, j - 1 ≤ k.val ∧ z k ≠ z' k) :
    Disjoint (cZ z +ᵥ interior (Dil N K j)) (cZ z' +ᵥ interior (Dil N K j)) := by
  refine Set.disjoint_left.mpr fun y hy1 hy2 => ?_
  rw [mem_vadd_set] at hy1 hy2
  obtain ⟨y1, hy1mem, hy1eq⟩ := hy1
  obtain ⟨y2, hy2mem, hy2eq⟩ := hy2
  have hsum' : cZ z +ᵥ y1 = cZ z' +ᵥ y2 := by rw [hy1eq, hy2eq]
  have hdiff : y1 - y2 = cZ (z' - z) := by
    funext k
    have hk : (z k : ℝ) + y1 k = (z' k : ℝ) + y2 k := by
      have h := congrFun hsum' k
      simpa [cZ] using h
    simp only [cZ, Pi.sub_apply]
    push_cast
    linarith
  have hgauge_lt : gauge K (y1 - y2) < lam N K j := by
    have h1 := gauge_lt_half_of_mem_interior_Dil hconv hsym hjpos hy1mem
    have h2 := gauge_lt_half_of_mem_interior_Dil hconv hsym hjpos hy2mem
    have habs := absorbent_of_convex_symm hconv hsym hint
    calc gauge K (y1 - y2) = gauge K (y1 + (-y2)) := by rw [sub_eq_add_neg]
      _ ≤ gauge K y1 + gauge K (-y2) := gauge_add_le hconv habs _ _
      _ = gauge K y1 + gauge K y2 := by rw [gauge_neg hsym]
      _ < lam N K j := by linarith
  have hlt : gauge K (cZ (z' - z)) < lam N K j := by rw [← hdiff]; exact hgauge_lt
  obtain ⟨k, hk, hkne⟩ := hne
  have hzero := hexcl j hj1 hjN (z' - z) hlt k hk
  simp only [Pi.sub_apply] at hzero
  exact hkne (sub_eq_zero.mp hzero).symm

/-- The Minkowski sum of the box of lattice points with the interior of `Dil j`. -/
noncomputable def boxSum (N : ℕ) (K : Set (Fin N → ℝ)) (q j : ℕ) : Set (Fin N → ℝ) :=
  ⋃ z ∈ boxVec N q, (z +ᵥ interior (Dil N K j))

/-- The Minkowski sum of the flag part of the box of lattice points with the interior of
`Dil j`. -/
noncomputable def flagSum (N : ℕ) (K : Set (Fin N → ℝ)) (q i j : ℕ) : Set (Fin N → ℝ) :=
  ⋃ p ∈ flagVec N q i, (p +ᵥ interior (Dil N K j))

/-- The volume of the Minkowski sum of the box of lattice points with the interior of `Dil j`. -/
noncomputable def Vq (N : ℕ) (K : Set (Fin N → ℝ)) (q j : ℕ) : ℝ :=
  volume.real (boxSum N K q j)

/-- Henk's eq. (second_two): the value of `Vq` for `j = 1`, where the translates are pairwise
disjoint by minimality of the first successive minimum. -/
lemma Vq_one (q : ℕ) (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K) (hclosed : IsClosed K)
    (hbdd : Bornology.IsBounded K) (hint : (interior K).Nonempty) (hN : 1 ≤ N)
    (hexcl : ∀ (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓN : ℓ ≤ N) (y : Fin N → ℤ),
      gauge K (cZ y) < lam N K ℓ → ∀ j : Fin N, ℓ - 1 ≤ j.val → y j = 0) :
    Vq N K q 1 = (2*q+1)^N * (lam N K 1 / 2)^N * (volume K).toReal := by
  have hjpos : 0 < lam N K 1 := lam_pos_of hconv hsym hbdd hint le_rfl hN
  have hpd : Set.PairwiseDisjoint (↑(boxVec N q) : Set (Fin N → ℝ))
      (fun z => z +ᵥ interior (Dil N K 1)) := by
    intro z hz z' hz' hne
    obtain ⟨wz, -, hzw⟩ := (mem_boxVec N q z).mp hz
    obtain ⟨wz', -, hz'w⟩ := (mem_boxVec N q z').mp hz'
    rw [hzw, hz'w]
    refine disjoint_translates_interior_Dil (j := 1) le_rfl hN hjpos hconv hsym hint hexcl ?_
    have hne' : wz ≠ wz' := by
      intro h; exact hne (by rw [hzw, hz'w, h])
    obtain ⟨k, hk⟩ : ∃ k, wz k ≠ wz' k := by
      by_contra h
      push Not at h
      exact hne' (funext h)
    exact ⟨k, by omega, hk⟩
  have hmeas : ∀ b ∈ boxVec N q, MeasurableSet (b +ᵥ interior (Dil N K 1)) :=
    fun b _ => (isOpen_interior.vadd b).measurableSet
  have hfin : ∀ b ∈ boxVec N q, volume (b +ᵥ interior (Dil N K 1)) ≠ ⊤ := by
    intro b _
    rw [measure_vadd]
    refine ne_of_lt ?_
    calc volume (interior (Dil N K 1)) ≤ volume (Dil N K 1) := measure_mono interior_subset
      _ = ENNReal.ofReal (|(lam N K 1 / 2)|^N) * volume K := by
            rw [Dil, Measure.addHaar_smul, Module.finrank_fin_fun, abs_pow]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbdd.measure_lt_top
  have hterm : ∀ p ∈ boxVec N q,
      volume.real (p +ᵥ interior (Dil N K 1)) = volume.real (interior (Dil N K 1)) := by
    intro p _
    rw [Measure.real_def, Measure.real_def, measure_vadd]
  rw [Vq, boxSum, measureReal_biUnion_finset hpd hmeas hfin, Finset.sum_congr rfl hterm,
    Finset.sum_const, card_boxVec, nsmul_eq_mul]
  rw [volume_real_interior_Dil hconv hclosed hsym hjpos]
  push_cast
  ring




variable {N : ℕ} {K : Set (Fin N → ℝ)}

/-- A coordinate bound for the dilated body `Dil j`. -/
lemma exists_coord_bound_Dil (hbdd : Bornology.IsBounded K) (j : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ Dil N K j, ∀ k : Fin N, |x k| ≤ R := by
  obtain ⟨R₀, hR₀, hb⟩ := exists_coord_bound N hbdd
  refine ⟨|lam N K j / 2| * R₀, by positivity, ?_⟩
  rintro x ⟨y, hy, rfl⟩ k
  show |((lam N K j / 2) • y) k| ≤ |lam N K j / 2| * R₀
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hb y hy k) (abs_nonneg _)

/-- The volume of a cube of half-side `a`. -/
lemma volume_real_pi_Icc (N : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    volume.real (Set.pi Set.univ (fun _ : Fin N => Set.Icc (-a) a)) = (2*a)^N := by
  have hcube : volume (Set.pi Set.univ (fun _ : Fin N => Set.Icc (-a) a))
      = ENNReal.ofReal ((2*a)^N) := by
    rw [volume_pi, Measure.pi_pi]
    have h : ∀ i : Fin N, volume (Set.Icc (-a) a) = ENNReal.ofReal (2*a) := by
      intro i; rw [Real.volume_Icc, show a - (-a) = 2*a from by ring]
    rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ 2*a)]
  rw [Measure.real_def, hcube, ENNReal.toReal_ofReal (by positivity)]

/-- The union of the translates of the interior of `Dil j` by the box of lattice points is
contained in the cube of half-side `q + R`. -/
lemma Vq_subset_cube (q j : ℕ) {R : ℝ}
    (hbound : ∀ x ∈ Dil N K j, ∀ k : Fin N, |x k| ≤ R) :
    (⋃ z ∈ boxVec N q, (z +ᵥ interior (Dil N K j))) ⊆
      Set.pi Set.univ (fun _ : Fin N => Set.Icc (-(q+R)) (q+R)) := by
  intro x hx
  simp only [mem_iUnion, mem_vadd_set, vadd_eq_add] at hx
  obtain ⟨z, hz, x', hx', rfl⟩ := hx
  obtain ⟨w, hw, hzw⟩ := (mem_boxVec N q z).mp hz
  rw [Set.mem_pi]
  intro k _
  have h1 : |z k| ≤ (q:ℝ) := by
    have hk := hw k
    have hzk : z k = (w k : ℝ) := congrFun hzw k
    rw [hzk]
    exact_mod_cast hk
  have h2 : |x' k| ≤ R := hbound x' (interior_subset hx') k
  have h3 : |z k + x' k| ≤ q + R := by
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith
  rw [Set.mem_Icc]
  exact abs_le.mp h3

/-- Henk's bound (second_one): `Vq` at the top level is at most a cube. -/
lemma Vq_le_cube (q j : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ x ∈ Dil N K j, ∀ k : Fin N, |x k| ≤ R) :
    Vq N K q j ≤ (2*(q + R))^N := by
  have hsub := Vq_subset_cube (K := K) q j hbound
  have hcube : volume (Set.pi Set.univ (fun _ : Fin N => Set.Icc (-(q+R)) (q+R)))
      = ENNReal.ofReal ((2*(q+R))^N) := by
    rw [volume_pi, Measure.pi_pi]
    have h : ∀ i : Fin N, volume (Set.Icc (-(q+R)) (q+R)) = ENNReal.ofReal (2*(q+R)) := by
      intro i; rw [Real.volume_Icc, show q+R - (-(q+R)) = 2*(q+R) from by ring]
    rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ 2*(q+R))]
  rw [Vq, measureReal_def]
  calc (volume (⋃ z ∈ boxVec N q, (z +ᵥ interior (Dil N K j)))).toReal
      ≤ (volume (Set.pi Set.univ (fun _ : Fin N => Set.Icc (-(q+R)) (q+R)))).toReal := by
        apply ENNReal.toReal_mono
        · rw [hcube]; exact ENNReal.ofReal_ne_top
        · exact measure_mono hsub
    _ = (2*(q+R))^N := by rw [hcube, ENNReal.toReal_ofReal (by positivity)]


variable {N : ℕ} {K : Set (Fin N → ℝ)}

/-- **Henk's eq. (cut)**, in the form needed for the splitting step: two lattice vectors differing
in a coordinate `≥ i` translate `flagSum` to disjoint sets, provided `i ≥ j - 1` (so that the
strong exclusion property at level `j` applies). -/
lemma disjoint_translates_flag (q i j : ℕ) (hiN : i ≤ N) (hj1 : 1 ≤ j) (hjN : j ≤ N)
    (hji : j - 1 ≤ i) (hjpos : 0 < lam N K j)
    (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty)
    (hexcl : ∀ (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓN : ℓ ≤ N) (y : Fin N → ℤ),
      gauge K (cZ y) < lam N K ℓ → ∀ j : Fin N, ℓ - 1 ≤ j.val → y j = 0)
    {t t' : Fin N → ℤ} (hne : ∃ k : Fin N, i ≤ k.val ∧ t k ≠ t' k) :
    Disjoint (cZ t +ᵥ flagSum N K q i j) (cZ t' +ᵥ flagSum N K q i j) := by
  set S := interior (Dil N K j) with hS
  rw [show flagSum N K q i j = (⋃ p ∈ flagVec N q i, (p +ᵥ S)) by
        rw [flagSum, hS]]
  refine Set.disjoint_left.mpr fun y hy1 hy2 => ?_
  rw [mem_vadd_set] at hy1 hy2
  obtain ⟨w1, hw1, hy1⟩ := hy1
  obtain ⟨w2, hw2, hy2⟩ := hy2
  simp only [vadd_eq_add] at hy1 hy2
  simp only [mem_iUnion, mem_vadd_set, vadd_eq_add] at hw1 hw2
  obtain ⟨p, hp, s, hs, hw1e⟩ := hw1
  obtain ⟨p', hp', s', hs', hw2e⟩ := hw2
  rw [mem_flagVec] at hp hp'
  obtain ⟨wp, hwp, hpw⟩ := (mem_boxVec N q p).mp hp.1
  obtain ⟨wp', hwp', hp'w⟩ := (mem_boxVec N q p').mp hp'.1
  have hmain : cZ t + w1 = cZ t' + w2 := hy1.trans hy2.symm
  have hpwk : ∀ k, p k = (wp k : ℝ) := fun k => congrFun hpw k
  have hp'wk : ∀ k, p' k = (wp' k : ℝ) := fun k => congrFun hp'w k
  have hdiff : s - s' = cZ ((t' - t) + (wp' - wp)) := by
    funext k
    have h := congrFun hmain k
    simp only [Pi.add_apply, cZ] at h
    rw [← hw1e, ← hw2e] at h
    simp only [Pi.add_apply] at h
    rw [hpwk k, hp'wk k] at h
    simp only [cZ, Pi.sub_apply, Pi.add_apply]
    push_cast
    linarith
  have hgauge : gauge K (cZ ((t' - t) + (wp' - wp))) < lam N K j := by
    rw [← hdiff]
    have habs := absorbent_of_convex_symm hconv hsym hint
    calc gauge K (s - s') = gauge K (s + (-s')) := by rw [sub_eq_add_neg]
      _ ≤ gauge K s + gauge K (-s') := gauge_add_le hconv habs _ _
      _ = gauge K s + gauge K s' := by rw [gauge_neg hsym]
      _ < lam N K j := by
            have h1 := gauge_lt_half_of_mem_interior_Dil hconv hsym hjpos hs
            have h2 := gauge_lt_half_of_mem_interior_Dil hconv hsym hjpos hs'
            linarith
  obtain ⟨k, hk, hkne⟩ := hne
  have hzero := hexcl j hj1 hjN ((t' - t) + (wp' - wp)) hgauge k (by omega)
  have hwpk : wp k = 0 := by
    have h : p k = 0 := hp.2 k hk
    rw [hpwk k] at h
    exact_mod_cast h
  have hwp'k : wp' k = 0 := by
    have h : p' k = 0 := hp'.2 k hk
    rw [hp'wk k] at h
    exact_mod_cast h
  simp only [Pi.add_apply, Pi.sub_apply] at hzero
  simp only [hwpk, hwp'k, sub_self, add_zero] at hzero
  exact hkne (sub_eq_zero.mp hzero).symm

/-- **The splitting step** (Henk, displayed equation before (second_five)): the volume of the
Minkowski sum of the box of lattice points with `Dil j` equals `|transvVec|` times the volume of
the Minkowski sum with the flag part of the box. -/
lemma Vq_split (q i j : ℕ) (hiN : i ≤ N) (hj1 : 1 ≤ j) (hjN : j ≤ N) (hji : j - 1 ≤ i)
    (hjpos : 0 < lam N K j) (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K)
    (hint : (interior K).Nonempty) (hbdd : Bornology.IsBounded K)
    (hexcl : ∀ (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓN : ℓ ≤ N) (y : Fin N → ℤ),
      gauge K (cZ y) < lam N K ℓ → ∀ j : Fin N, ℓ - 1 ≤ j.val → y j = 0) :
    Vq N K q j = ((transvVec N q i).card : ℝ) * volume.real (flagSum N K q i j) := by
  set S := interior (Dil N K j) with hS
  have hset : boxSum N K q j = ⋃ t ∈ transvVec N q i, (t +ᵥ flagSum N K q i j) := by
    rw [flagSum]
    ext y
    rw [boxSum]
    simp only [mem_iUnion, mem_vadd_set, vadd_eq_add]
    constructor
    · rintro ⟨z, hz, s, hs, rfl⟩
      obtain ⟨t, ht, p, hp, hzp⟩ := boxVec_decomp N q i hz
      refine ⟨t, ht, p + s, ?_, by rw [hzp]; abel⟩
      exact ⟨p, hp, s, hs, rfl⟩
    · rintro ⟨t, ht, w, hw, rfl⟩
      obtain ⟨p, hp, s, hs, rfl⟩ := hw
      exact ⟨t + p, boxVec_prod_mem N q i ht hp, s, hs, by abel⟩
  obtain ⟨R, hR, hbound⟩ := exists_coord_bound_Dil (N := N) (K := K) hbdd j
  have hcube : volume (Set.pi Set.univ (fun _ : Fin N => Set.Icc (-(q+R)) (q+R)))
      = ENNReal.ofReal ((2*(q+R))^N) := by
    rw [volume_pi, Measure.pi_pi]
    have h : ∀ k : Fin N, volume (Set.Icc (-(q+R)) (q+R)) = ENNReal.ofReal (2*(q+R)) := by
      intro k; rw [Real.volume_Icc, show q+R - (-(q+R)) = 2*(q+R) from by ring]
    rw [Finset.prod_congr rfl (fun k _ => h k), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ 2*(q+R))]
  have hWsub : flagSum N K q i j ⊆ Set.pi Set.univ (fun _ : Fin N => Set.Icc (-(q+R)) (q+R)) := by
    intro x hx
    simp only [flagSum, mem_iUnion, mem_vadd_set, vadd_eq_add] at hx
    obtain ⟨p, hp, s, hs, rfl⟩ := hx
    rw [mem_flagVec] at hp
    obtain ⟨wp, hwp, hpw⟩ := (mem_boxVec N q p).mp hp.1
    rw [Set.mem_pi]
    intro k _
    have h1 : |p k| ≤ (q:ℝ) := by
      have hk := hwp k
      have hpk : p k = (wp k : ℝ) := congrFun hpw k
      rw [hpk]; exact_mod_cast hk
    have h2 : |s k| ≤ R := hbound s (interior_subset hs) k
    have h3 : |p k + s k| ≤ q + R := by
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith
    rw [Set.mem_Icc]
    exact abs_le.mp h3
  have hfinW : volume (flagSum N K q i j) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono hWsub) ?_)
    rw [hcube]; exact ENNReal.ofReal_lt_top
  have hpd : Set.PairwiseDisjoint (↑(transvVec N q i) : Set (Fin N → ℝ))
      (fun t => t +ᵥ flagSum N K q i j) := by
    intro t ht t' ht' hne
    rw [Finset.mem_coe, mem_transvVec] at ht ht'
    obtain ⟨wt, -, htw⟩ := (mem_boxVec N q t).mp ht.1
    obtain ⟨wt', -, ht'w⟩ := (mem_boxVec N q t').mp ht'.1
    rw [htw, ht'w]
    refine disjoint_translates_flag q i j hiN hj1 hjN hji hjpos hconv hsym hint hexcl ?_
    have hne' : wt ≠ wt' := by intro h; exact hne (by rw [htw, ht'w, h])
    obtain ⟨k, hk⟩ : ∃ k, wt k ≠ wt' k := by
      by_contra h; push Not at h; exact hne' (funext h)
    refine ⟨k, ?_, hk⟩
    by_contra hlt
    push Not at hlt
    have h1 : (wt k : ℝ) = 0 := by simpa [htw] using ht.2 k hlt
    have h2 : (wt' k : ℝ) = 0 := by simpa [ht'w] using ht'.2 k hlt
    exact hk (by exact_mod_cast (h1.trans h2.symm))
  have hmeas : ∀ b ∈ transvVec N q i, MeasurableSet (b +ᵥ flagSum N K q i j) := by
    intro b _
    have hopen : IsOpen (flagSum N K q i j) := by
      rw [flagSum]
      exact isOpen_biUnion (fun p _ => isOpen_interior.vadd p)
    exact (hopen.vadd b).measurableSet
  have hfin : ∀ b ∈ transvVec N q i, volume (b +ᵥ flagSum N K q i j) ≠ ⊤ := by
    intro b _
    rw [measure_vadd]
    exact hfinW
  have hsum : ∑ b ∈ transvVec N q i, volume.real (b +ᵥ flagSum N K q i j)
      = ∑ _b ∈ transvVec N q i, volume.real (flagSum N K q i j) :=
    Finset.sum_congr rfl fun b _ => by rw [Measure.real_def, Measure.real_def, measure_vadd]
  rw [Vq, hset, measureReal_biUnion_finset hpd hmeas hfin, hsum, Finset.sum_const, nsmul_eq_mul]


variable {N : ℕ} {K : Set (Fin N → ℝ)}

/-- A union of translates written as a Minkowski sum. -/
lemma biUnion_vadd_eq_add (S : Finset (Fin N → ℝ)) (A : Set (Fin N → ℝ)) :
    (⋃ z ∈ S, (z +ᵥ A)) = (↑S : Set (Fin N → ℝ)) + A := by
  ext x
  simp only [mem_iUnion, mem_vadd_set, vadd_eq_add, Finset.mem_coe, Set.mem_add]
  constructor
  · rintro ⟨z, hz, a, ha, rfl⟩; exact ⟨z, hz, a, ha, rfl⟩
  · rintro ⟨z, hz, a, ha, rfl⟩; exact ⟨z, hz, a, ha, rfl⟩

/-- A nonzero dilation of a closed set is closed. -/
lemma isClosed_smul_of_ne_zero (hclosed : IsClosed K) {c : ℝ} (hc : c ≠ 0) :
    IsClosed (c • K) := by
  have h : c • K = (fun x : Fin N → ℝ => c⁻¹ • x) ⁻¹' K := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc]
    rfl
  rw [h]
  exact hclosed.preimage (continuous_const_smul _)

/-- The diagonal linear map scaling the first `i` coordinates by `a` and the remaining ones
by `b`. -/
noncomputable def flagDiag (N i : ℕ) (a b : ℝ) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) where
  toFun x := fun k => if k.val < i then a * x k else b * x k
  map_add' x y := by
    funext k; simp only [Pi.add_apply]
    by_cases h : k.val < i <;> simp [h, mul_add]
  map_smul' c x := by
    funext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    by_cases h : k.val < i <;> simp [h] <;> ring

lemma flagDiag_apply (N i : ℕ) (a b : ℝ) (x : Fin N → ℝ) (k : Fin N) :
    flagDiag N i a b x k = if k.val < i then a * x k else b * x k := rfl

lemma flagDiag_comp (N i : ℕ) (a b c d : ℝ) (x : Fin N → ℝ) :
    flagDiag N i a b (flagDiag N i c d x) = flagDiag N i (a*c) (b*d) x := by
  funext k; simp only [flagDiag_apply]
  by_cases h : k.val < i <;> simp [h] <;> ring

lemma flagDiag_smul_self (N i : ℕ) (c : ℝ) (x : Fin N → ℝ) :
    flagDiag N i c c x = c • x := by
  funext k; simp only [flagDiag_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : k.val < i <;> simp [h]

/-- The absolute value of the determinant of `flagDiag`. -/
lemma abs_det_flagDiag {N i : ℕ} (hi : i ≤ N) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |LinearMap.det (flagDiag N i a b)| = a^i * b^(N-i) := by
  have heq : flagDiag N i a b
      = Matrix.toLin' (Matrix.diagonal (fun k : Fin N => if k.val < i then a else b)) := by
    apply LinearMap.ext
    intro x
    funext k
    rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
    simp only [flagDiag_apply]
    by_cases h : k.val < i <;> simp [h]
  rw [heq, LinearMap.det_toLin', Matrix.det_diagonal, prod_flag_ite hi, abs_mul, abs_pow, abs_pow,
    abs_of_nonneg ha, abs_of_nonneg hb]

/-- The volume of the image of a set under a linear map. -/
lemma volume_real_image_linearMap (f : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) (S : Set (Fin N → ℝ)) :
    volume.real (f '' S) = |LinearMap.det f| * volume.real S := by
  rw [Measure.real_def, Measure.addHaar_image_linearMap, Measure.real_def, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]

/-- `f₂ '' (M + f₁ '' A) = M + ρ • A` for the two diagonal maps `f₁ = flagDiag ρ 1`,
`f₂ = flagDiag 1 ρ`, when `M` is supported on the first `i` coordinates. -/
lemma flagDiag_image_add (N i : ℕ) (ρ : ℝ) (M A : Set (Fin N → ℝ))
    (hM : ∀ x ∈ M, ∀ k : Fin N, i ≤ k.val → x k = 0) :
    flagDiag N i 1 ρ '' (M + flagDiag N i ρ 1 '' A) = M + (fun a => ρ • a) '' A := by
  have hd : ∀ a : Fin N → ℝ, flagDiag N i 1 ρ (flagDiag N i ρ 1 a) = ρ • a := by
    intro a
    rw [flagDiag_comp]
    funext k; simp only [flagDiag_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : k.val < i <;> simp [h]
  have hfix : ∀ m ∈ M, flagDiag N i 1 ρ m = m := by
    intro m hm
    funext k
    by_cases h : k.val < i
    · simp only [flagDiag_apply, if_pos h, one_mul]
    · have hzero : m k = 0 := hM m hm k (not_lt.mp h)
      simp only [flagDiag_apply, if_neg h, hzero, mul_zero]
  ext y
  constructor
  · rintro ⟨z, hz, hfz⟩
    obtain ⟨m, hm, a', ha', hma'⟩ := hz
    obtain ⟨a, ha, hfa⟩ := ha'
    exact ⟨m, hm, ρ • a, ⟨a, ha, rfl⟩,
      by rw [← hfz, ← hma', map_add, hfix m hm, ← hfa, hd a]⟩
  · rintro ⟨m, hm, a', ha', hma'⟩
    obtain ⟨a, ha, hfa⟩ := ha'
    exact ⟨m + flagDiag N i ρ 1 a, ⟨m, hm, flagDiag N i ρ 1 a, ⟨a, ha, rfl⟩, rfl⟩,
      by rw [map_add, hfix m hm, hd a, ← hma', ← hfa]⟩

/-- `ρ • Dil i = Dil (i+1)` for `ρ = λ_{i+1}/λ_i`. -/
lemma image_smul_Dil {i : ℕ} {ρ : ℝ} (hρ : ρ = lam N K (i+1) / lam N K i)
    (hlam : lam N K i ≠ 0) :
    (fun a : Fin N → ℝ => ρ • a) '' Dil N K i = Dil N K (i+1) := by
  have hcoef : ρ * (lam N K i / 2) = lam N K (i+1) / 2 := by
    rw [hρ]; field_simp
  rw [Dil, Dil, image_smul, smul_smul, hcoef]

/-- The `volume.real` version of `volume_biUnion_translates_interior`, in terms of `flagSum`. -/
lemma volume_real_biUnion_Dil (q i j : ℕ) (hconv : Convex ℝ K) :
    volume.real (⋃ p ∈ flagVec N q i, (p +ᵥ Dil N K j)) = volume.real (flagSum N K q i j) := by
  rw [flagSum, Measure.real_def, Measure.real_def, Dil]
  rw [volume_biUnion_translates_interior (hA := hconv.smul _) (S := flagVec N q i)]




variable {N : ℕ} {K : Set (Fin N → ℝ)}

/-- Translating a set by a single vector does not change its Lebesgue measure. -/
lemma volume_image_add_const (S : Set (Fin N → ℝ)) (t : Fin N → ℝ) :
    volume ((fun x : Fin N → ℝ => x + t) '' S) = volume S := by
  have h : (fun x : Fin N → ℝ => x + t) '' S = (fun h : Fin N → ℝ => h + (-t)) ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨y - t, by simpa [sub_eq_add_neg] using hy, by abel⟩
  rw [h, measure_preimage_add_right]

lemma smul_combination_add (b c : Fin N → ℝ) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    (ρ • ((1/ρ) • b + ((ρ-1)/ρ) • c)) + (1-ρ) • c = b := by
  have hρne : ρ ≠ 0 := by linarith
  rw [smul_add, smul_smul, smul_smul]
  rw [mul_one_div_cancel hρne, one_smul]
  have hcoef : ρ * ((ρ - 1) / ρ) = ρ - 1 := by field_simp
  rw [hcoef]
  module

/-- **Scaling a convex set by `ρ ≥ 1` does not decrease the volume of a Minkowski sum.** -/
lemma volume_add_smul_le (M B : Set (Fin N → ℝ)) (hB : Convex ℝ B) (hBne : B.Nonempty)
    {ρ : ℝ} (hρ : 1 ≤ ρ) : volume (M + B) ≤ volume (M + ρ • B) := by
  obtain ⟨c, hc⟩ := hBne
  have hsub : M + B ⊆ (fun x : Fin N → ℝ => x + ((1 - ρ) • c)) '' (M + ρ • B) := by
    rintro x ⟨m, hm, b, hb, rfl⟩
    have ha' : (1/ρ) • b + ((ρ-1)/ρ) • c ∈ B :=
      hB hb hc (by positivity) (by positivity) (by field_simp; ring)
    refine ⟨m + ρ • ((1/ρ) • b + ((ρ-1)/ρ) • c),
      ⟨m, hm, ρ • ((1/ρ) • b + ((ρ-1)/ρ) • c), ⟨_, ha', rfl⟩, rfl⟩, ?_⟩
    show (m + ρ • ((1/ρ) • b + ((ρ-1)/ρ) • c)) + (1 - ρ) • c = m + b
    rw [add_assoc, smul_combination_add b c hρ]
  calc volume (M + B) ≤ volume ((fun x : Fin N → ℝ => x + ((1 - ρ) • c)) '' (M + ρ • B)) :=
        measure_mono hsub
    _ = volume (M + ρ • B) := volume_image_add_const _ _

/-- **Scaling a convex set by `ρ ≥ 1` does not decrease the volume of a Minkowski sum**
(no nonemptiness assumption). -/
lemma volume_add_smul_le' (M B : Set (Fin N → ℝ)) (hB : Convex ℝ B) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    volume (M + B) ≤ volume (M + ρ • B) := by
  rcases Set.eq_empty_or_nonempty B with h | hne
  · simp [h]
  · exact volume_add_smul_le M B hB hne hρ

/-- The linear map splitting `ℝ^N` into the first `i` and the last `N - i` coordinates. -/
noncomputable def splitMap (i N : ℕ) (hi : i ≤ N) :
    (Fin N → ℝ) →ₗ[ℝ] ((Fin i → ℝ) × (Fin (N - i) → ℝ)) where
  toFun x := (fun k => x (Fin.castLE hi k), fun k => x ⟨i + k.val, by omega⟩)
  map_add' x y := by
    apply Prod.ext <;> funext k <;> simp
  map_smul' c x := by
    apply Prod.ext <;> funext k <;> simp

@[simp] lemma splitMap_fst (i N : ℕ) (hi : i ≤ N) (x : Fin N → ℝ) :
    (splitMap i N hi x).1 = fun k => x (Fin.castLE hi k) := rfl

@[simp] lemma splitMap_snd (i N : ℕ) (hi : i ≤ N) (x : Fin N → ℝ) :
    (splitMap i N hi x).2 = fun k => x ⟨i + k.val, by omega⟩ := rfl

lemma splitMap_injective (i N : ℕ) (hi : i ≤ N) : Function.Injective (splitMap i N hi) := by
  intro x y h
  funext k
  by_cases hk : k.val < i
  · have h1 : x (Fin.castLE hi ⟨k.val, hk⟩) = y (Fin.castLE hi ⟨k.val, hk⟩) := by
      have := congrFun (congrArg Prod.fst h) ⟨k.val, hk⟩
      simpa only [splitMap_fst] using this
    have hcast : Fin.castLE hi ⟨k.val, hk⟩ = k := Fin.ext rfl
    rwa [hcast] at h1
  · have h2 : x (⟨i + (k.val - i), by omega⟩ : Fin N) = y ⟨i + (k.val - i), by omega⟩ := by
      have := congrFun (congrArg Prod.snd h) ⟨k.val - i, by omega⟩
      simpa only [splitMap_snd] using this
    have hcast : (⟨i + (k.val - i), by omega⟩ : Fin N) = k := Fin.ext (by simp; omega)
    rwa [hcast] at h2

lemma splitMap_surjective (i N : ℕ) (hi : i ≤ N) : Function.Surjective (splitMap i N hi) := by
  intro p
  refine ⟨fun k => if h : k.val < i then p.1 ⟨k.val, h⟩ else p.2 ⟨k.val - i, by omega⟩, ?_⟩
  have h1 : (splitMap i N hi (fun k => if h : k.val < i then p.1 ⟨k.val, h⟩
      else p.2 ⟨k.val - i, by omega⟩)).1 = p.1 := by
    funext k
    simp only [splitMap_fst, Fin.val_castLE, dif_pos k.isLt]
  have h2 : (splitMap i N hi (fun k => if h : k.val < i then p.1 ⟨k.val, h⟩
      else p.2 ⟨k.val - i, by omega⟩)).2 = p.2 := by
    funext k
    simp only [splitMap_snd]
    have hk : ¬ ((⟨i + k.val, by omega⟩ : Fin N).val < i) := by simp
    rw [dif_neg hk]
    have hfin : (⟨i + k.val - i, by omega⟩ : Fin (N - i)) = k := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [hfin]
  exact Prod.ext h1 h2

lemma measurePreserving_splitMap (i N : ℕ) (hi : i ≤ N) :
    MeasurePreserving (splitMap i N hi) volume volume := by
  obtain ⟨e₀, hmp, ha, hb⟩ := measure_preserving_fin_split i N hi
  have hfun : ⇑(splitMap i N hi) = ⇑e₀ := by
    funext x
    apply Prod.ext
    · show (fun k : Fin i => x (Fin.castLE hi k)) = (e₀ x).1
      exact (ha x).symm
    · show (fun k : Fin (N - i) => x ⟨i + k.val, by omega⟩) = (e₀ x).2
      funext k
      exact (congrFun (hb x) k).symm
  rw [hfun]
  exact hmp

lemma measurableSet_image_splitMap (i N : ℕ) (hi : i ≤ N) {S : Set (Fin N → ℝ)}
    (hS : MeasurableSet S) : MeasurableSet ((splitMap i N hi) '' S) := by
  obtain ⟨e₀, hmp, ha, hb⟩ := measure_preserving_fin_split i N hi
  have hfun : ⇑(splitMap i N hi) = ⇑e₀ := by
    funext x
    apply Prod.ext
    · show (fun k : Fin i => x (Fin.castLE hi k)) = (e₀ x).1
      exact (ha x).symm
    · show (fun k : Fin (N - i) => x ⟨i + k.val, by omega⟩) = (e₀ x).2
      funext k
      exact (congrFun (hb x) k).symm
  have hset : (splitMap i N hi) '' S = (e₀.symm) ⁻¹' S := by
    rw [show (splitMap i N hi) '' S = e₀ '' S from by rw [hfun]]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨e₀.symm y, hy, by simp⟩
  rw [hset]
  exact hS.preimage e₀.symm.measurable

/-- **Fubini slicing along the first `i` coordinates.** -/
lemma volume_eq_lintegral_slice (i N : ℕ) (hi : i ≤ N) {S : Set (Fin N → ℝ)}
    (hS : MeasurableSet S) :
    volume S = ∫⁻ w : Fin (N - i) → ℝ,
      volume {u : Fin i → ℝ | (u, w) ∈ (splitMap i N hi) '' S} := by
  have hmp := measurePreserving_splitMap i N hi
  have hmeas : Measurable (splitMap i N hi) :=
    (splitMap i N hi).continuous_of_finiteDimensional.measurable
  have hSmeas := measurableSet_image_splitMap i N hi hS
  have h1 : (volume.prod volume) ((splitMap i N hi) '' S) = volume S := by
    have hmap : (volume.prod volume) = Measure.map (splitMap i N hi) volume := hmp.map_eq.symm
    rw [hmap, Measure.map_apply hmeas hSmeas]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [splitMap_injective i N hi hyx] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [← h1]
  exact Measure.prod_apply_symm hSmeas

/-- Slices of a Minkowski sum in a product. -/
lemma slice_prod_add {E F : Type*} [AddCommMonoid E] [AddCommMonoid F]
    (P Q : Set (E × F)) (hP : ∀ p ∈ P, p.2 = 0) (w : F) :
    {u : E | (u, w) ∈ P + Q} = {u : E | (u, 0) ∈ P} + {u : E | (u, w) ∈ Q} := by
  ext u
  constructor
  · rintro ⟨p, hp, q, hq, hpq⟩
    have hpw : p.2 = 0 := hP p hp
    have hq2 : q.2 = w := by
      have h := congrArg Prod.snd hpq
      rw [Prod.snd_add, hpw, zero_add] at h
      exact h
    have hp' : (p.1, (0 : F)) ∈ P := by
      have h : (p.1, (0 : F)) = p := Prod.ext rfl hpw.symm
      rw [h]; exact hp
    have hq' : (q.1, w) ∈ Q := by
      have h : (q.1, w) = q := Prod.ext rfl hq2.symm
      rw [h]; exact hq
    have hu : u = p.1 + q.1 := by
      have h := congrArg Prod.fst hpq
      rw [Prod.fst_add] at h
      exact h.symm
    exact ⟨p.1, hp', q.1, hq', hu.symm⟩
  · rintro ⟨u₁, hu₁, u₂, hu₂, rfl⟩
    exact ⟨(u₁, 0), hu₁, (u₂, w), hu₂, by
      show (u₁, (0:F)) + (u₂, w) = (u₁ + u₂, w)
      rw [Prod.mk_add_mk, zero_add]⟩

lemma convex_slice_splitMap (i N : ℕ) (hi : i ≤ N) {A : Set (Fin N → ℝ)}
    (hA : Convex ℝ A) (w : Fin (N - i) → ℝ) :
    Convex ℝ {u : Fin i → ℝ | (u, w) ∈ (splitMap i N hi) '' A} := by
  intro u hu v hv a b ha hb hab
  obtain ⟨au, hau, huφ⟩ := hu
  obtain ⟨av, hav, hvφ⟩ := hv
  have hu2 : (splitMap i N hi au).2 = w := (Prod.ext_iff.mp huφ).2
  have hv2 : (splitMap i N hi av).2 = w := (Prod.ext_iff.mp hvφ).2
  have hsum : a • au + b • av ∈ A := hA hau hav ha hb hab
  refine ⟨a • au + b • av, hsum, ?_⟩
  have h1 : (splitMap i N hi (a • au + b • av)).1 = a • u + b • v := by
    rw [map_add, map_smul, map_smul, Prod.fst_add, Prod.smul_fst, Prod.smul_fst,
      (Prod.ext_iff.mp huφ).1, (Prod.ext_iff.mp hvφ).1]
  have h2 : (splitMap i N hi (a • au + b • av)).2 = w := by
    rw [map_add, map_smul, map_smul, Prod.snd_add, Prod.smul_snd, Prod.smul_snd, hu2, hv2,
      ← add_smul, hab, one_smul]
  exact Prod.ext h1 h2

/-- The `splitMap`-image of the flag-scaled set, componentwise. -/
lemma splitMap_flagScaled (i N : ℕ) (hi : i ≤ N) (ρ : ℝ) (a : Fin N → ℝ) :
    splitMap i N hi (fun k => if k.val < i then ρ * a k else a k)
      = (ρ • (splitMap i N hi a).1, (splitMap i N hi a).2) := by
  apply Prod.ext
  · funext k
    simp only [splitMap_fst, Pi.smul_apply, smul_eq_mul, Fin.val_castLE, if_pos k.isLt]
  · funext k
    simp only [splitMap_snd]
    rw [if_neg (by omega)]

lemma slice_image_flagScaled (i N : ℕ) (hi : i ≤ N) {A : Set (Fin N → ℝ)} {ρ : ℝ}
    (w : Fin (N - i) → ℝ) :
    {u : Fin i → ℝ | (u, w) ∈ (splitMap i N hi) ''
        ((fun x : Fin N → ℝ => fun k => if k.val < i then ρ * x k else x k) '' A)}
      = ρ • {u : Fin i → ℝ | (u, w) ∈ (splitMap i N hi) '' A} := by
  ext u
  constructor
  · rintro ⟨a, ⟨a₀, ha₀, rfl⟩, huφ⟩
    rw [splitMap_flagScaled] at huφ
    exact ⟨(splitMap i N hi a₀).1,
      ⟨a₀, ha₀, Prod.ext rfl (Prod.ext_iff.mp huφ).2⟩, (Prod.ext_iff.mp huφ).1⟩
  · rintro ⟨u₀, hu₀, rfl⟩
    obtain ⟨a₀, ha₀, haφ⟩ := hu₀
    exact ⟨(fun k => if k.val < i then ρ * a₀ k else a₀ k), ⟨a₀, ha₀, rfl⟩,
      by rw [splitMap_flagScaled, haφ]⟩

/-- `φ '' M` has zero second coordinate when `M` is supported on the first `i` coordinates. -/
lemma splitMap_image_snd_zero (i N : ℕ) (hi : i ≤ N) {M : Set (Fin N → ℝ)}
    (hM : ∀ x ∈ M, ∀ k : Fin N, i ≤ k.val → x k = 0) {p : (Fin i → ℝ) × (Fin (N - i) → ℝ)}
    (hp : p ∈ (splitMap i N hi) '' M) : p.2 = 0 := by
  obtain ⟨m, hm, rfl⟩ := hp
  funext k
  simp only [splitMap_snd, Pi.zero_apply]
  exact hM m hm _ (by simp)



lemma measurableSet_add_finite (M A : Set (Fin N → ℝ)) (hMfin : M.Finite) (hAcl : IsClosed A) :
    MeasurableSet (M + A) := by
  rw [← hMfin.coe_toFinset, ← biUnion_vadd_eq_add hMfin.toFinset A]
  refine (isClosed_biUnion_finset (fun m _ => ?_)).measurableSet
  show IsClosed ((m : Fin N → ℝ) +ᵥ A)
  rw [show (m : Fin N → ℝ) +ᵥ A = (fun y : Fin N → ℝ => m + y) '' A from rfl]
  exact (Homeomorph.isClosed_image (Homeomorph.addLeft (G := Fin N → ℝ) m)).mpr hAcl

/-- The `flagDiag`-scaling equals the image of the inverse scaling. -/
lemma flagScaled_image_eq_preimage (i N : ℕ) (hi : i ≤ N) {ρ : ℝ} (hρ : 0 < ρ)
    {A : Set (Fin N → ℝ)} :
    (fun x : Fin N → ℝ => fun k => if k.val < i then ρ * x k else x k) '' A
      = (flagDiag N i (1/ρ) 1) ⁻¹' A := by
  have hrinv : ρ * (1/ρ) = 1 := by field_simp
  have hcomp : ∀ (u v : ℝ) (h : u * v = 1) (y : Fin N → ℝ),
      flagDiag N i u 1 (flagDiag N i v 1 y) = y := by
    intro u v huv y
    rw [flagDiag_comp, huv]
    funext k
    simp only [flagDiag_apply]
    by_cases h : k.val < i <;> simp [h]
  have hleft : ∀ y : Fin N → ℝ,
      (flagDiag N i ρ 1) (flagDiag N i (1/ρ) 1 y) = y := hcomp ρ (1/ρ) hrinv
  have hleft2 : ∀ y : Fin N → ℝ,
      (flagDiag N i (1/ρ) 1) (flagDiag N i ρ 1 y) = y := by
    have hrinv2 : (1/ρ) * ρ = 1 := by field_simp
    exact hcomp (1/ρ) ρ hrinv2
  have hright : ∀ a : Fin N → ℝ,
      (fun x : Fin N → ℝ => fun k => if k.val < i then ρ * x k else x k) a
        = (flagDiag N i ρ 1) a := by
    intro a
    funext k
    simp only [flagDiag_apply]
    by_cases h : k.val < i <;> simp [h]
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Set.mem_preimage, hright a, hleft2]
    exact ha
  · intro hy
    exact ⟨(flagDiag N i (1/ρ) 1) y, hy, by rw [hright, hleft]⟩

lemma measurableSet_add_flagScaled (i N : ℕ) (hi : i ≤ N) (M A : Set (Fin N → ℝ))
    (hMfin : M.Finite) (hAcl : IsClosed A) {ρ : ℝ} (hρ : 0 < ρ) :
    MeasurableSet (M + (fun x : Fin N → ℝ => fun k => if k.val < i then ρ * x k else x k) '' A) := by
  have hopen : IsClosed ((fun x : Fin N → ℝ => fun k => if k.val < i then ρ * x k else x k) '' A) := by
    rw [flagScaled_image_eq_preimage i N hi hρ]
    exact hAcl.preimage (LinearMap.continuous_of_finiteDimensional (flagDiag N i (1/ρ) 1))
  exact measurableSet_add_finite M _ hMfin hopen

/-- **Scaling the flag directions does not decrease the volume of a Minkowski sum**
(Henk, arXiv:math/0204158, eq. (second_six)); straightened form. -/
lemma volume_minkowski_flag_scale_aux (N : ℕ) {A : Set (Fin N → ℝ)} (hA : Convex ℝ A)
    (hAcl : IsClosed A) (M : Set (Fin N → ℝ)) (hMfin : M.Finite) (i : ℕ) (hi : i ≤ N)
    (hM : ∀ x ∈ M, ∀ k : Fin N, i ≤ k.val → x k = 0) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    volume (M + A) ≤
      volume (M + (fun x : Fin N → ℝ => fun k => if k.val < i then ρ * x k else x k) '' A) := by
  have hρpos : 0 < ρ := by linarith
  have hSmeas : MeasurableSet (M + A) := measurableSet_add_finite M A hMfin hAcl
  have hTmeas : MeasurableSet (M +
      (fun x : Fin N → ℝ => fun k => if k.val < i then ρ * x k else x k) '' A) :=
    measurableSet_add_flagScaled i N hi M A hMfin hAcl hρpos
  have eS := volume_eq_lintegral_slice i N hi hSmeas
  have eT := volume_eq_lintegral_slice i N hi hTmeas
  have hpt : ∀ w : Fin (N - i) → ℝ,
      volume {u : Fin i → ℝ | (u, w) ∈ (splitMap i N hi) '' (M + A)}
        ≤ volume {u : Fin i → ℝ | (u, w) ∈ (splitMap i N hi) ''
            (M + (fun x : Fin N → ℝ => fun k => if k.val < i then ρ * x k else x k) '' A)} := by
    intro w
    have h1 : {u : Fin i → ℝ | (u, w) ∈ (splitMap i N hi) '' (M + A)}
        = {u : Fin i → ℝ | (u, 0) ∈ (splitMap i N hi) '' M}
          + {u : Fin i → ℝ | (u, w) ∈ (splitMap i N hi) '' A} := by
      rw [image_add]
      exact slice_prod_add (E := Fin i → ℝ) (F := Fin (N - i) → ℝ)
        ((splitMap i N hi) '' M) ((splitMap i N hi) '' A)
        (fun p hp => splitMap_image_snd_zero i N hi hM hp) w
    have h2 : {u : Fin i → ℝ | (u, w) ∈ (splitMap i N hi) ''
            (M + (fun x : Fin N → ℝ => fun k => if k.val < i then ρ * x k else x k) '' A)}
        = {u : Fin i → ℝ | (u, 0) ∈ (splitMap i N hi) '' M}
          + {u : Fin i → ℝ | (u, w) ∈ (splitMap i N hi) ''
              ((fun x : Fin N → ℝ => fun k => if k.val < i then ρ * x k else x k) '' A)} := by
      rw [image_add]
      exact slice_prod_add (E := Fin i → ℝ) (F := Fin (N - i) → ℝ)
        ((splitMap i N hi) '' M)
        ((splitMap i N hi) '' ((fun x : Fin N → ℝ => fun k => if k.val < i then ρ * x k else x k) '' A))
        (fun p hp => splitMap_image_snd_zero i N hi hM hp) w
    have h3 : {u : Fin i → ℝ | (u, w) ∈ (splitMap i N hi) ''
              ((fun x : Fin N → ℝ => fun k => if k.val < i then ρ * x k else x k) '' A)}
        = ρ • {u : Fin i → ℝ | (u, w) ∈ (splitMap i N hi) '' A} :=
      slice_image_flagScaled i N hi w
    rw [h1, h2, h3]
    exact volume_add_smul_le' _ _ (convex_slice_splitMap i N hi hA w) hρ
  calc volume (M + A)
      = ∫⁻ w : Fin (N - i) → ℝ, volume {u : Fin i → ℝ | (u, w) ∈ (splitMap i N hi) '' (M + A)} := eS
    _ ≤ ∫⁻ w : Fin (N - i) → ℝ,
          volume {u : Fin i → ℝ | (u, w) ∈ (splitMap i N hi) ''
            (M + (fun x : Fin N → ℝ => fun k => if k.val < i then ρ * x k else x k) '' A)} :=
        lintegral_mono hpt
    _ = volume (M + (fun x : Fin N → ℝ => fun k => if k.val < i then ρ * x k else x k) '' A) := eT.symm


variable {N : ℕ} {K : Set (Fin N → ℝ)}

/-- The translates of the `flagDiag`-image of `Dil i` by the flag box are contained in a cube,
hence have finite measure. -/
lemma volume_lt_top_flagDiag_Dil (q i : ℕ) (hbdd : Bornology.IsBounded K) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    volume ((↑(flagVec N q i) : Set (Fin N → ℝ)) + flagDiag N i ρ 1 '' Dil N K i) < ⊤ := by
  obtain ⟨R, hR, hbound⟩ := exists_coord_bound_Dil (N := N) (K := K) hbdd i
  set C := ρ * R with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hsub : ((↑(flagVec N q i) : Set (Fin N → ℝ)) + flagDiag N i ρ 1 '' Dil N K i) ⊆
      Set.pi Set.univ (fun _ : Fin N => Set.Icc (-(q+C)) (q+C)) := by
    rintro x ⟨m, hm, y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hy
    rw [Finset.mem_coe, mem_flagVec] at hm
    rw [Set.mem_pi]
    intro k _
    have hmk : |m k| ≤ (q:ℝ) := by
      obtain ⟨w, hw, hwm⟩ := (mem_boxVec N q m).mp hm.1
      have hmk' : m k = (w k : ℝ) := congrFun hwm k
      rw [hmk']; exact_mod_cast hw k
    have hzk : |z k| ≤ R := hbound z hz k
    have hyk : |flagDiag N i ρ 1 z k| ≤ C := by
      rw [flagDiag_apply]
      by_cases h : k.val < i
      · rw [if_pos h, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ ρ), hC]
        exact mul_le_mul_of_nonneg_left hzk (by linarith : (0:ℝ) ≤ ρ)
      · rw [if_neg h, one_mul]
        calc |z k| ≤ R := hzk
          _ ≤ ρ * R := le_mul_of_one_le_left hR hρ
    have h3 : |m k + flagDiag N i ρ 1 z k| ≤ q + C := by
      rw [abs_le] at hmk hyk ⊢
      constructor <;> linarith
    rw [Set.mem_Icc]
    exact abs_le.mp h3
  calc volume ((↑(flagVec N q i) : Set (Fin N → ℝ)) + flagDiag N i ρ 1 '' Dil N K i)
      ≤ volume (Set.pi Set.univ (fun _ : Fin N => Set.Icc (-(q+C)) (q+C))) := measure_mono hsub
    _ = ENNReal.ofReal ((2*(q+C))^N) := by
        rw [volume_pi, Measure.pi_pi]
        have h : ∀ k : Fin N, volume (Set.Icc (-(q+C)) (q+C)) = ENNReal.ofReal (2*(q+C)) := by
          intro k; rw [Real.volume_Icc, show q+C - (-(q+C)) = 2*(q+C) from by ring]
        rw [Finset.prod_congr rfl (fun k _ => h k), Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ 2*(q+C))]
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- The image of `A` under the lambda-scaling map of the crux lemma equals the image under
`flagDiag ρ 1`. -/
lemma image_lambda_flagDiag (i : ℕ) (ρ : ℝ) (A : Set (Fin N → ℝ)) :
    (fun x : Fin N → ℝ => fun k => if k.val < i then ρ * x k else x k) '' A
      = flagDiag N i ρ 1 '' A := by
  have hfun : ∀ x : Fin N → ℝ,
      (fun k => if k.val < i then ρ * x k else x k) = flagDiag N i ρ 1 x := by
    intro x
    funext k; rw [flagDiag_apply]
    by_cases h : k.val < i <;> simp [h]
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, (hfun x).symm.trans hxy⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, (hfun x).trans hxy⟩

/-- **Henk's inequality (second_three)**: one step of the telescoping. -/
lemma Vq_step (q i : ℕ) (hi1 : 1 ≤ i) (hiN' : i + 1 ≤ N) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hclosed : IsClosed K) (hbdd : Bornology.IsBounded K)
    (hint : (interior K).Nonempty)
    (hexcl : ∀ (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓN : ℓ ≤ N) (y : Fin N → ℤ),
      gauge K (cZ y) < lam N K ℓ → ∀ j : Fin N, ℓ - 1 ≤ j.val → y j = 0) :
    (lam N K (i+1) / lam N K i)^(N-i) * Vq N K q i ≤ Vq N K q (i+1) := by
  have hiN : i ≤ N := by omega
  have hjpos : 0 < lam N K i := lam_pos_of hconv hsym hbdd hint hi1 hiN
  have hjpos' : 0 < lam N K (i+1) := lam_pos_of hconv hsym hbdd hint (by omega) hiN'
  obtain ⟨r, hr, hball⟩ := exists_ball_subset hconv hsym hint
  have hle : lam N K i ≤ lam N K (i+1) := lam_mono N K hr hball (by omega) hiN'
  set ρ := lam N K (i+1) / lam N K i with hρdef
  have hρ1 : 1 ≤ ρ := by rw [hρdef, le_div_iff₀ hjpos]; linarith
  -- the splitting identities
  have hsi := Vq_split q i i hiN hi1 hiN (by omega) hjpos hconv hsym hint hbdd hexcl
  have hsi1 := Vq_split q i (i+1) hiN (by omega) hiN' (by omega) hjpos' hconv hsym hint hbdd hexcl
  -- the key inequality for the flag sums
  have hkey : ρ^(N-i) * volume.real (flagSum N K q i i)
      ≤ volume.real (flagSum N K q i (i+1)) := by
    set M : Set (Fin N → ℝ) := (↑(flagVec N q i) : Set (Fin N → ℝ)) with hMdef
    have hM : ∀ x ∈ M, ∀ k : Fin N, i ≤ k.val → x k = 0 := by
      intro x hx k hk
      rw [hMdef, Finset.mem_coe, mem_flagVec] at hx
      exact hx.2 k hk
    have hMfin : M.Finite := by rw [hMdef]; exact Finset.finite_toSet _
    have e1 : volume.real (flagSum N K q i i) = volume.real (M + Dil N K i) := by
      rw [← volume_real_biUnion_Dil q i i hconv, biUnion_vadd_eq_add, ← hMdef]
    have e2 : volume.real (flagSum N K q i (i+1)) = volume.real (M + Dil N K (i+1)) := by
      rw [← volume_real_biUnion_Dil q i (i+1) hconv, biUnion_vadd_eq_add, ← hMdef]
    have hf2 : flagDiag N i 1 ρ '' (M + flagDiag N i ρ 1 '' Dil N K i) = M + Dil N K (i+1) := by
      rw [flagDiag_image_add N i ρ M (Dil N K i) hM,
        image_smul_Dil (N := N) (K := K) hρdef (ne_of_gt hjpos)]
    have hdet : |LinearMap.det (flagDiag N i 1 ρ)| = ρ^(N-i) := by
      rw [abs_det_flagDiag hiN (by norm_num) (by linarith)]
      norm_num
    have hvol : volume.real (M + Dil N K (i+1))
        = ρ^(N-i) * volume.real (M + flagDiag N i ρ 1 '' Dil N K i) := by
      rw [← hf2, volume_real_image_linearMap, hdet]
    have hcrux : volume (M + Dil N K i)
        ≤ volume (M + flagDiag N i ρ 1 '' Dil N K i) := by
      have h := volume_minkowski_flag_scale_aux (N := N) (A := Dil N K i)
        (hconv.smul (lam N K i / 2))
        (isClosed_smul_of_ne_zero (K := K) hclosed (by positivity)) M hMfin i
        (by omega) hM hρ1
      rwa [image_lambda_flagDiag] at h
    have hfin : volume (M + flagDiag N i ρ 1 '' Dil N K i) ≠ ⊤ := by
      rw [hMdef]; exact ne_of_lt (volume_lt_top_flagDiag_Dil (K := K) q i hbdd hρ1)
    have hcruxR : volume.real (M + Dil N K i)
        ≤ volume.real (M + flagDiag N i ρ 1 '' Dil N K i) := ENNReal.toReal_mono hfin hcrux
    calc ρ^(N-i) * volume.real (flagSum N K q i i)
        = ρ^(N-i) * volume.real (M + Dil N K i) := by rw [e1]
      _ ≤ ρ^(N-i) * volume.real (M + flagDiag N i ρ 1 '' Dil N K i) :=
          mul_le_mul_of_nonneg_left hcruxR (pow_nonneg (by linarith) _)
      _ = volume.real (M + Dil N K (i+1)) := hvol.symm
      _ = volume.real (flagSum N K q i (i+1)) := e2.symm
  calc (lam N K (i+1) / lam N K i)^(N-i) * Vq N K q i
      = ((transvVec N q i).card : ℝ) * (ρ^(N-i) * volume.real (flagSum N K q i i)) := by
        rw [hsi, ← hρdef]; ring
    _ ≤ ((transvVec N q i).card : ℝ) * volume.real (flagSum N K q i (i+1)) :=
        mul_le_mul_of_nonneg_left hkey (Nat.cast_nonneg _)
    _ = Vq N K q (i+1) := hsi1.symm




variable {N : ℕ} {K : Set (Fin N → ℝ)}

/-- **Minkowski's second theorem, upper bound, in straightened form** (proved from the
Minkowski/box chain of Henk's paper). -/
theorem minkowski_second_upper_flag (N : ℕ) (K : Set (Fin N → ℝ))
    (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K) (hclosed : IsClosed K)
    (hbdd : Bornology.IsBounded K) (hint : (interior K).Nonempty)
    (hexcl : ∀ (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓN : ℓ ≤ N) (y : Fin N → ℤ),
      gauge K (cZ y) < lam N K ℓ → ∀ j : Fin N, ℓ - 1 ≤ j.val → y j = 0) :
    (∏ i : Fin N, lam N K (i.val + 1)) * (volume K).toReal ≤ 2^N := by
  classical
  rcases N with _ | M
  · -- `N = 0`
    have huniv : volume (Set.univ : Set (Fin 0 → ℝ)) = 1 := by
      rw [volume_pi, Measure.pi_univ]; simp
    have hle : volume K ≤ 1 := by
      rw [← huniv]; exact measure_mono (subset_univ K)
    have := ENNReal.toReal_mono ENNReal.one_ne_top hle
    simpa using this
  · -- `N = M + 1 ≥ 1`
    rw [Fin.prod_univ_eq_prod_range (fun i => lam (M+1) K (i + 1)) (M+1)]
    set a : ℕ → ℝ := fun j => lam (M+1) K (j + 1) with hadef
    have hapos : ∀ j ≤ M, 0 < a j := by
      intro j hj
      rw [hadef]
      exact lam_pos_of hconv hsym hbdd hint (by omega) (by omega)
    -- the chain of Henk's inequality (second_three)
    have hchain : ∀ q : ℕ, (∏ j ∈ Finset.Icc 1 M, (a j / a (j-1))^(M+1-j)) * Vq (M+1) K q 1
        ≤ Vq (M+1) K q (M+1) := by
      intro q
      have key : ∀ m, m ≤ M →
          (∏ j ∈ Finset.Icc 1 m, (a j / a (j-1))^(M+1-j)) * Vq (M+1) K q 1
            ≤ Vq (M+1) K q (m+1) := by
        intro m
        induction m with
        | zero => intro _; simp
        | succ m ih =>
          intro hm
          have hm' : m ≤ M := by omega
          have hih := ih hm'
          rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1)]
          have hstep := Vq_step (N := M+1) (K := K) q (m+1) (by omega) (by omega)
            hconv hsym hclosed hbdd hint hexcl
          have hcoe : (a (m+1) / a (m+1-1))^(M+1-(m+1))
              = (lam (M+1) K (m+1+1) / lam (M+1) K (m+1))^(M+1-(m+1)) := by
            rw [hadef]; norm_num
          rw [hcoe]
          calc ((∏ j ∈ Finset.Icc 1 m, (a j / a (j-1))^(M+1-j)) * (a (m+1) / a (m+1-1))^(M+1-(m+1)))
                * Vq (M+1) K q 1
              = (a (m+1) / a (m+1-1))^(M+1-(m+1))
                  * ((∏ j ∈ Finset.Icc 1 m, (a j / a (j-1))^(M+1-j)) * Vq (M+1) K q 1) := by
                ring
            _ ≤ (a (m+1) / a (m+1-1))^(M+1-(m+1)) * Vq (M+1) K q (m+1) :=
                mul_le_mul_of_nonneg_left hih (by
                  apply pow_nonneg
                  exact div_nonneg (le_of_lt (hapos (m+1) (by omega)))
                    (le_of_lt (hapos (m+1-1) (by omega))))
            _ ≤ Vq (M+1) K q (m+1+1) := hstep
      exact key M le_rfl
    -- the telescoping product identity
    have htel : (∏ j ∈ Finset.Icc 1 M, (a j / a (j-1))^(M+1-j)) * (a 0 / 2)^(M+1)
        = (∏ j ∈ Finset.range (M+1), a j) / 2^(M+1) :=
      prod_ratio_pow_telescope (d := M+1) a (fun j hj => ne_of_gt (hapos j (by omega)))
    -- the value of `Vq q 1`
    have hone : ∀ q : ℕ, Vq (M+1) K q 1
        = (2*(q:ℝ)+1)^(M+1) * (a 0 / 2)^(M+1) * (volume K).toReal := by
      intro q
      have h := Vq_one (N := M+1) (K := K) q hconv hsym hclosed hbdd hint (by omega) hexcl
      simpa [hadef, Nat.cast_add, Nat.cast_mul, mul_add] using h
    -- the cube bound
    obtain ⟨R, hR, hbound⟩ := exists_coord_bound_Dil (N := M+1) (K := K) hbdd (M+1)
    have hcube := fun q => Vq_le_cube (N := M+1) (K := K) q (M+1) hR hbound
    -- the main inequality for every `q`
    have hmain : ∀ q : ℕ, (2*(q:ℝ)+1)^(M+1) * ((∏ j ∈ Finset.range (M+1), a j) / 2^(M+1))
          * (volume K).toReal ≤ (2*(q:ℝ)+2*R)^(M+1) := by
      intro q
      have h1 := hchain q
      have h2 := hone q
      have h3 := hcube q
      calc (2*(q:ℝ)+1)^(M+1) * ((∏ j ∈ Finset.range (M+1), a j) / 2^(M+1))
            * (volume K).toReal
          = (∏ j ∈ Finset.Icc 1 M, (a j / a (j-1))^(M+1-j)) * Vq (M+1) K q 1 := by
            rw [h2, ← htel]; ring
        _ ≤ Vq (M+1) K q (M+1) := h1
        _ ≤ (2*(q:ℝ)+2*R)^(M+1) := by
            have := h3
            rwa [show (2*((q:ℝ) + R)) = 2*(q:ℝ)+2*R from by ring] at this
    -- limit `q → ∞`
    have hratio : ∀ q : ℕ,
        (∏ j ∈ Finset.range (M+1), a j) * (volume K).toReal / 2^(M+1)
          ≤ ((2*(q:ℝ)+2*R) / (2*(q:ℝ)+1))^(M+1) := by
      intro q
      have h := hmain q
      have hq : (0:ℝ) < (2*(q:ℝ)+1)^(M+1) := pow_pos (by positivity) _
      have hdiv := div_le_div_of_nonneg_right h (le_of_lt hq)
      have hsimp : (2*(q:ℝ)+1)^(M+1) * ((∏ j ∈ Finset.range (M+1), a j) / 2^(M+1))
            * (volume K).toReal / (2*(q:ℝ)+1)^(M+1)
          = (∏ j ∈ Finset.range (M+1), a j) * (volume K).toReal / 2^(M+1) := by
        field_simp
      have hsimp2 : (2*(q:ℝ)+2*R)^(M+1) / (2*(q:ℝ)+1)^(M+1)
          = ((2*(q:ℝ)+2*R)/(2*(q:ℝ)+1))^(M+1) := by rw [div_pow]
      rw [hsimp, hsimp2] at hdiv
      exact hdiv
    have htend : Tendsto (fun q : ℕ => ((2*(q:ℝ)+2*R) / (2*(q:ℝ)+1))^(M+1)) atTop (𝓝 1) := by
      have h0 : Tendsto (fun q : ℕ => (2*(q:ℝ)+2*R) / (2*(q:ℝ)+1)) atTop (𝓝 1) := by
        have heq : (fun q : ℕ => (2*(q:ℝ)+2*R) / (2*(q:ℝ)+1))
            = fun q : ℕ => 1 + (2*R-1) / (2*(q:ℝ)+1) := by
          funext q; field_simp; ring
        rw [heq]
        have hdiv : Tendsto (fun q : ℕ => (2*R-1) / (2*(q:ℝ)+1)) atTop (𝓝 0) := by
          apply Tendsto.div_atTop tendsto_const_nhds
          have h2 : Tendsto (fun q : ℕ => 2*(q:ℝ)) atTop atTop :=
            tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
          simpa using tendsto_atTop_add_const_right _ (1:ℝ) h2
        simpa using tendsto_const_nhds.add hdiv
      simpa using h0.pow (M+1)
    have hlim := le_of_tendsto_of_tendsto tendsto_const_nhds htend
      (Filter.Eventually.of_forall hratio)
    -- `hlim : (∏ a) * volK / 2^(M+1) ≤ 1`
    have h2k : (0:ℝ) < 2^(M+1) := by positivity
    have := mul_le_mul_of_nonneg_right hlim (le_of_lt h2k)
    rw [div_mul_cancel₀ _ (ne_of_gt h2k), one_mul] at this
    simpa using this




variable {N : ℕ} {K : Set (Fin N → ℝ)}

/-- Membership in the span of the first `M` standard basis vectors forces the tail coordinates
to vanish. -/
lemma eq_zero_of_mem_span_prefix {M N : ℕ} (hm : M ≤ N) {w : Fin N → ℤ}
    (h : cZ w ∈ Submodule.span ℝ
      (Set.range (fun j : Fin M => (Pi.single (Fin.castLE hm j) (1:ℝ) : Fin N → ℝ))))
    (k : Fin N) (hk : M ≤ k.val) : w k = 0 := by
  have hspan : Submodule.span ℝ (Set.range (fun j : Fin M =>
      (Pi.single (Fin.castLE hm j) (1:ℝ) : Fin N → ℝ)))
      ≤ LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) k) := by
    rw [Submodule.span_le]
    rintro y ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply]
    show (Pi.single (Fin.castLE hm j) (1:ℝ) : Fin N → ℝ) k = 0
    rw [Pi.single_eq_of_ne]
    intro hEq
    have hv : (Fin.castLE hm j).val = k.val := by rw [hEq]
    simp only [Fin.val_castLE] at hv
    omega
  have hmem := hspan h
  rw [LinearMap.mem_ker, LinearMap.proj_apply] at hmem
  simp only [cZ] at hmem
  exact_mod_cast hmem

/-- **Minkowski's second theorem, upper bound, for the lattice `ℤ^N`** (the sharp constant),
in the "straightened" normal form where the successive-minima flag is the standard coordinate
flag.  Inlined `λ j = sInf {t > 0 : t • K contains j linearly independent integer vectors}`. -/
theorem minkowski_second_upper_of_exclusion (N : ℕ) (K : Set (Fin N → ℝ))
    (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K) (hclosed : IsClosed K)
    (hbdd : Bornology.IsBounded K) (hint : (interior K).Nonempty)
    (hexcl : ∀ (i : ℕ) (hi : 1 ≤ i) (w : Fin N → ℤ),
      gauge K (fun k => (w k : ℝ)) <
        sInf {t : ℝ | 0 < t ∧ ∃ v : Fin i → (Fin N → ℤ),
          LinearIndependent ℝ (fun a => fun k => (v a k : ℝ)) ∧
          ∀ a, (fun k => (v a k : ℝ)) ∈ t • K} →
      ∀ j : Fin N, i ≤ j.val → w j = 0) :
    (∏ i : Fin N, sInf {t : ℝ | 0 < t ∧ ∃ v : Fin (i.val + 1) → (Fin N → ℤ),
        LinearIndependent ℝ (fun a => fun k => (v a k : ℝ)) ∧
        ∀ a, (fun k => (v a k : ℝ)) ∈ t • K}) * (volume K).toReal ≤ 2^N := by
  classical
  obtain ⟨v, hvLI, _hvmin, hvexc⟩ := gauge_realizers_exclusion N K hconv hsym hclosed hbdd hint
  obtain ⟨U, hUZ, hUZi, hUdet, hUflag⟩ := exists_unimodular_flag N v hvLI
  have hUdet_ne : LinearMap.det U ≠ 0 := abs_ne_zero.mp (by rw [hUdet]; exact one_ne_zero)
  let Ue : (Fin N → ℝ) ≃ₗ[ℝ] (Fin N → ℝ) := U.equivOfDetNeZero hUdet_ne
  have hUe : ∀ x : Fin N → ℝ, Ue x = U x := fun x => rfl
  set K' : Set (Fin N → ℝ) := U '' K with hK'def
  -- the transported structure
  have hconv' : Convex ℝ K' := by rw [hK'def]; exact hconv.linear_image U
  have hsym' : ∀ x ∈ K', -x ∈ K' := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨-y, hsym y hy, by rw [map_neg]⟩
  have hclosed' : IsClosed K' := by
    rw [hK'def]
    have hset : U '' K = (Ue.symm : (Fin N → ℝ) → (Fin N → ℝ)) ⁻¹' K := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        show Ue.symm (Ue y) ∈ K
        rwa [LinearEquiv.symm_apply_apply]
      · intro hx
        exact ⟨Ue.symm x, hx, (hUe (Ue.symm x)).trans (LinearEquiv.apply_symm_apply Ue x)⟩
    rw [hset, show (Ue.symm : (Fin N → ℝ) → (Fin N → ℝ)) = ⇑(Ue.symm : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) from rfl]
    exact hclosed.preimage (LinearMap.continuous_of_finiteDimensional _)
  have hbdd' : Bornology.IsBounded K' := by
    rw [hK'def]
    have h := Bornology.IsBounded.image
      (f := (Ue.toContinuousLinearEquiv : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) hbdd
    simpa [hUe] using h
  have hcoe : (⇑Ue.toContinuousLinearEquiv.toHomeomorph : (Fin N → ℝ) → (Fin N → ℝ)) = U := by
    funext x
    exact hUe x
  have hint' : (interior K').Nonempty := by
    rw [hK'def]
    have h := (Homeomorph.image_interior Ue.toContinuousLinearEquiv.toHomeomorph K).symm
    rw [hcoe] at h
    rw [h]
    exact Set.Nonempty.image _ hint
  -- the strong exclusion property for `K'`
  have hexcl' : ∀ (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓN : ℓ ≤ N) (y : Fin N → ℤ),
      gauge K' (cZ y) < lam N K' ℓ → ∀ j : Fin N, ℓ - 1 ≤ j.val → y j = 0 := by
    intro ℓ hℓ1 hℓN y hyg j hj
    obtain ⟨x, hx⟩ := hUZi y
    obtain ⟨hlam, -, hgauge⟩ := successive_minima_unimodular N K hconv hsym hclosed hint
      U hUZ hUZi hUdet ℓ
    have hlam' : lam N K' ℓ = lam N K ℓ := by simpa [lam, hK'def] using hlam
    have h3 := hgauge (fun k => (x k : ℝ))
    have hg : gauge K (fun k => (x k : ℝ)) = gauge K' (fun k => (y k : ℝ)) := by
      have h3' : gauge K' (fun k => (y k : ℝ)) = gauge K (fun k => (x k : ℝ)) := by
        rw [← hx]
        exact h3
      exact h3'.symm
    have hlt : gauge K (fun k => (x k : ℝ)) < lam N K ℓ := by
      rw [hg, ← hlam']
      change gauge K' (cZ y) < lam N K' ℓ
      exact hyg
    have hspan := hvexc ℓ hℓ1 hℓN x (by simpa [lam] using hlt)
    have hmemU : U (fun k => (x k : ℝ)) ∈ U '' (Submodule.span ℝ (Set.range (fun j : Fin (ℓ - 1) =>
        (fun k => (v (Fin.castLE (by omega) j) k : ℝ))))) := ⟨_, hspan, rfl⟩
    rw [hUflag (ℓ - 1) (by omega)] at hmemU
    rw [hx] at hmemU
    exact eq_zero_of_mem_span_prefix (by omega) hmemU j hj
  -- apply the straightened form
  have hflag := minkowski_second_upper_flag N K' hconv' hsym' hclosed' hbdd' hint' hexcl'
  -- transport back
  have hlamall : ∀ ℓ : ℕ, lam N K' ℓ = lam N K ℓ := by
    intro ℓ
    obtain ⟨h1, -, -⟩ := successive_minima_unimodular N K hconv hsym hclosed hint U hUZ hUZi hUdet ℓ
    simpa [lam, hK'def] using h1
  have hvol : (volume K').toReal = (volume K).toReal := by
    obtain ⟨-, h2, -⟩ := successive_minima_unimodular N K hconv hsym hclosed hint U hUZ hUZi hUdet 0
    rw [Measure.real_def, Measure.real_def] at h2
    simpa [hK'def] using h2
  rw [Finset.prod_congr rfl (fun i _ => hlamall (i.val+1)), hvol] at hflag
  simpa [lam] using hflag

end Commons.GeometryOfNumbers.SuccessiveMinima

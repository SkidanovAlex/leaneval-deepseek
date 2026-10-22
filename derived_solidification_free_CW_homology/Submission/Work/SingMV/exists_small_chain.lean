import Mathlib
import Submission.Work.SINGMV.Defs
import Submission.Work.SingMV.bary_dist_le
import Submission.Work.SingMV.subBarycenter_dist_le
import Submission.Work.SingMV.affineSimplex_comp
import Submission.Work.SingMV.affineSimplex_subBarycenter
import Submission.Work.SingMV.toE_iConvexComb_subBarycenter
import Submission.Work.SingMV.sdMeshDefs
import Submission.Work.SingMV.SdAux
import Submission.Work.SingMV.Bdry_mem_affineSpan
import Submission.Work.SingMV.sddeg_aux
import Submission.Work.SingMV.sddeg_naturality
import Submission.Work.SingMV.exists_delta_small
import Submission.Work.SingMV.smallSpan_inf

/-!
# Every chain becomes small after enough barycentric subdivisions

This file proves `Work.SingMV.exists_small_chain`: for open `U, V ⊆ X` with `U ∪ V = X`, every
singular `n`-chain `z` of `X` becomes a `(U, V)`-small chain after enough applications of the
degreewise barycentric subdivision `sddeg X n`.

## Strategy

* The barycentric subdivision `Sd n` of the fundamental `n`-simplex is a linear combination of
  the affine `n`-simplices whose vertex tuples are barycentric subdivision tuples
  (`esc_sd_mem_tupSpan`); this is transported to the statement that the iterated subdivision
  `sdIter n k` lies in the span `meshSpan n n ((n/(n+1))^k)` of the `((n/(n+1))^k)`-close affine
  simplices (`esc_sdIter_mem_meshSpan`), i.e. the mesh of the subdivision shrinks by the factor
  `n/(n+1)` at each step.
* Pushing a small simplex forward along a singular simplex `σ` keeps it in the submodule of
  `(U,V)`-small chains, with "small" measured by the Lebesgue number of the open cover
  `{σ⁻¹U, σ⁻¹V}` (`exists_delta_small`, `esc_map_meshSpan_le_smallChain`).
* Combining these, every generator `gen X n σ` becomes small after enough subdivisions
  (`esc_gen_eventually_small`). Since `sddeg` is additive and its iterates are additive, the set
  of chains that *eventually* (for all large enough numbers of subdivisions) become small is a
  submodule containing all the generators, hence everything.

## Main result

* `Work.SingMV.exists_small_chain`. -/

open CategoryTheory Limits Convexity
open scoped BigOperators Simplicial

noncomputable section

set_option maxHeartbeats 1000000

namespace Work.SingMV

/-! ## Metric preliminaries -/

/-- Every tuple of points of `Δ^N` is `1`-close: the coordinates of the weights of a point of the
standard simplex lie in `[0,1]`. -/
lemma esc_vclose_one {N L : ℕ} (q : Fin L → StdSimplex ℝ (Fin (N+1))) : VClose q 1 := by
  intro i j
  refine (dist_pi_le_iff zero_le_one).2 fun k => ?_
  change |(q i).weights k - (q j).weights k| ≤ 1
  have h1 : (q i).weights k ≤ 1 := by
    have h := Finset.single_le_sum (s := Finset.univ) (f := fun l => (q i).weights l)
      (fun l _ => StdSimplex.weights_nonneg l) (Finset.mem_univ k)
    rwa [StdSimplex.total_of_fintype] at h
  have h2 : (q j).weights k ≤ 1 := by
    have h := Finset.single_le_sum (s := Finset.univ) (f := fun l => (q j).weights l)
      (fun l _ => StdSimplex.weights_nonneg l) (Finset.mem_univ k)
    rwa [StdSimplex.total_of_fintype] at h
  have h3 : 0 ≤ (q i).weights k := StdSimplex.weights_nonneg k
  have h4 : 0 ≤ (q j).weights k := StdSimplex.weights_nonneg k
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- The weights of the uniform distribution on a finite set of vertices of the standard simplex,
for an arbitrary index type. -/
lemma esc_weights_subBarycenter_apply {M : Type*} [DecidableEq M]
    (A : Finset M) (hA : A.Nonempty) (i : M) :
    (StdSimplex.subBarycenter (K := ℝ) A hA).weights i
      = if i ∈ A then (A.card : ℝ)⁻¹ else 0 := by
  rw [Convexity.StdSimplex.weights_subBarycenter]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

/-- Pushing the uniform distribution on a finite set of vertices forward along an injective map
gives the uniform distribution on the image. -/
lemma esc_subBarycenter_map {m : ℕ} (S : Finset (Fin m)) (hS : S.Nonempty)
    {N : Type*} [DecidableEq N] (f : Fin m → N) (hf : Function.Injective f) :
    (StdSimplex.subBarycenter (K := ℝ) S hS).map f =
      StdSimplex.subBarycenter (K := ℝ) (S.image f) (hS.image f) := by
  ext n
  rw [StdSimplex.weights_map]
  by_cases hn : n ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hn
    rw [Finsupp.mapDomain_apply_of_injective hf]
    rw [esc_weights_subBarycenter_apply S hS a,
      esc_weights_subBarycenter_apply (S.image f) (hS.image f) (f a)]
    simp only [Finset.card_image_of_injective S hf]
    have hiff : a ∈ S ↔ f a ∈ S.image f :=
      ⟨fun ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩,
        fun h => by
          obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp h
          rwa [hf hxa] at hx⟩
    by_cases hfa : f a ∈ S.image f
    · have ha : a ∈ S := hiff.mpr hfa
      simp [ha, hfa]
    · have ha : a ∉ S := fun h => hfa (hiff.mp h)
      simp [ha, hfa]
  · have hnot : ¬ (n ∈ S.image f) := by
      intro hmem
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hmem
      exact hn ⟨x, rfl⟩
    rw [Finsupp.mapDomain_of_notMem_range _ _ hn,
      esc_weights_subBarycenter_apply (S.image f) (hS.image f) n, if_neg hnot]

/-! ## The combinatorics of barycentric subdivision tuples -/

/-- Pushing a barycentric subdivision tuple forward along an injective map of vertex sets gives a
barycentric subdivision tuple. -/
lemma esc_tup_map {m L n : ℕ} {q : Fin L → StdSimplex ℝ (Fin (m+1))} (hq : Tup m L q)
    (f : Fin (m+1) → Fin (n+1)) (hf : Function.Injective f) :
    Tup n L (fun i => (q i).map f) := by
  obtain ⟨A, hA, hmono, rfl⟩ := hq
  refine ⟨fun i => (A i).image f, fun i => (hA i).image f,
    fun i j hij => Finset.image_subset_image (hmono i j hij), ?_⟩
  funext i
  exact esc_subBarycenter_map (A i) (hA i) f hf

/-- A barycentric subdivision tuple, extended by the barycenter of all vertices, is again a
barycentric subdivision tuple. -/
lemma esc_tup_snoc {m L : ℕ} {q : Fin L → StdSimplex ℝ (Fin (m+1))} (hq : Tup m L q) :
    Tup m (L+1) (Fin.snoc q (StdSimplex.subBarycenter (K := ℝ)
      (Finset.univ : Finset (Fin (m+1))) Finset.univ_nonempty)) := by
  obtain ⟨A, hA, hmono, rfl⟩ := hq
  refine ⟨Fin.snoc A (Finset.univ : Finset (Fin (m+1))), ?_, ?_, ?_⟩
  · intro i
    cases i using Fin.lastCases with
    | last => rw [Fin.snoc_last]; exact Finset.univ_nonempty
    | cast j => simpa using hA j
  · intro i j hij
    cases j using Fin.lastCases with
    | last => simp
    | cast j' =>
      cases i using Fin.lastCases with
      | last =>
        exfalso
        have h := Fin.le_iff_val_le_val.mp hij
        simp only [Fin.val_last, Fin.val_castSucc] at h
        have hj := j'.isLt
        omega
      | cast i' => simpa using hmono i' j' (Fin.castSucc_le_castSucc_iff.mp hij)
  · funext i
    cases i using Fin.lastCases with
    | last => simp
    | cast j => simp

/-! ## `tupSpan` closure and `Sd n ∈ tupSpan n n` -/

/-- The pushforward along a coface inclusion maps the span of the subdivision simplices of `Δ^m`
into the corresponding span for `Δ^{m+1}`. -/
lemma esc_map_tupSpan_coface (m l : ℕ) (i : Fin (m+2)) :
    Submodule.map (((Submission.Blueprint.singC).map (coface m i)).f l).hom (tupSpan m l) ≤
      tupSpan (m+1) l := by
  refine Submodule.map_le_iff_le_comap.mpr ?_
  rw [tupSpan]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨q, rfl⟩
  change ((Submission.Blueprint.singC).map (coface m i)).f l
      (gen (tSplx m) l (affineSimplex q.1)) ∈ tupSpan (m+1) l
  rw [gen_map, coface_comp_affineSimplex]
  exact gen_affineSimplex_mem_tupSpan
    (esc_tup_map q.2 i.succAbove Fin.succAbove_right_injective)

/-- The cone on a subdivision simplex with apex the barycenter of all vertices is a subdivision
simplex again: the cone over the span of the subdivision simplices of `Δ^m` lands in the span of
those of `Δ^m` in one degree higher. -/
lemma esc_map_tupSpan_coneChain (m l : ℕ) :
    Submodule.map (coneChain m (unif (Finset.univ : Finset (Fin (m+1))) Finset.univ_nonempty) l).hom
      (tupSpan m l) ≤ tupSpan m (l+1) := by
  refine Submodule.map_le_iff_le_comap.mpr ?_
  rw [tupSpan]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨q, rfl⟩
  change coneChain m (unif (Finset.univ : Finset (Fin (m+1))) Finset.univ_nonempty) l
      (gen (tSplx m) l (affineSimplex q.1)) ∈ tupSpan m (l+1)
  rw [coneChain_gen]
  rw [show (fun i : Fin (l+1) => affineSimplex (n := m) (k := l) q.1 (vert (l+1) i)) = q.1
    from funext fun i => affineSimplex_vert q.1 i]
  exact gen_affineSimplex_mem_tupSpan (esc_tup_snoc q.2)

/-- **The subdivision of the fundamental simplex is a combination of subdivision simplices.**
`Sd n` lies in the span of the generators attached to the barycentric subdivision tuples, i.e. to
increasing chains of barycenters of nonempty subsets of the vertices of `Δ^n`. -/
lemma esc_sd_mem_tupSpan (n : ℕ) : Sd n ∈ tupSpan n n := by
  induction n with
  | zero =>
      rw [show Sd 0 = gen (tSplx 0) 0 (ContinuousMap.id _) from rfl, ← affineSimplex_eq_id 0]
      apply gen_affineSimplex_mem_tupSpan
      have h := Tup.mk (M := 0) (L := 1) (fun i : Fin 1 => ({i} : Finset (Fin 1)))
        (fun i => Finset.singleton_nonempty i)
        (fun i j _ => by
          rw [Finset.singleton_subset_iff]
          exact Subsingleton.elim i j ▸ Finset.mem_singleton_self i)
      have htupeq : (fun i : Fin 1 =>
            StdSimplex.subBarycenter (K := ℝ) ({i} : Finset (Fin 1))
              (Finset.singleton_nonempty i)) = fun i : Fin 1 => vert 1 i := by
        funext i
        simp [vert]
      rwa [htupeq] at h
  | succ n ih =>
      rw [show Sd (n+1) = (-1 : ℤ) ^ (n+1) • coneChain (n+1)
        (unif (Finset.univ : Finset (Fin (n+2))) Finset.univ_nonempty) n
        (SdBdry n (Sd n)) from rfl]
      have hbdry : SdBdry n (Sd n) ∈ tupSpan (n+1) n := by
        rw [show SdBdry n (Sd n) = ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) •
          (((Submission.Blueprint.singC).map (coface n i)).f n (Sd n)) from rfl]
        exact (tupSpan (n+1) n).sum_mem (fun i _ =>
          smul_mem_int ((esc_map_tupSpan_coface n n i) (Submodule.mem_map_of_mem ih)) _)
      exact smul_mem_int ((esc_map_tupSpan_coneChain (n+1) n)
        (Submodule.mem_map_of_mem hbdry)) _

/-! ## The mesh shrinks under subdivision -/

/-- The metric estimate behind the shrinking of the mesh: the vertex tuple obtained by composing
a `d`-close tuple of vertices with a barycentric subdivision tuple of `Δ^n` is
`(n/(n+1)) · d`-close. -/
lemma esc_vclose_affineSimplex_comp {n : ℕ} {q : Fin (n+1) → StdSimplex ℝ (Fin (n+1))}
    {d : ℝ} (hq : VClose q d)
    {r : Fin (n+1) → StdSimplex ℝ (Fin (n+1))} (hr : Tup n (n+1) r) :
    VClose (fun i => affineSimplex q (r i)) (((n : ℝ)/((n : ℝ) + 1)) * d) := by
  obtain ⟨A, hA, hmono, hr'⟩ := hr
  have hd0 : 0 ≤ d := le_trans dist_nonneg (hq 0 0)
  have hfrac : ∀ k : ℕ, 1 ≤ k → k ≤ n+1 →
      (((k : ℝ) - 1) / k) ≤ (n : ℝ)/((n : ℝ) + 1) := by
    intro k hk1 hk2
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    rw [div_le_div_iff₀ hk0 (by positivity)]
    have hk2' : (k : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast hk2
    push_cast at hk2' ⊢
    nlinarith
  have hmain : VClose (fun i => iConvexComb (StdSimplex.subBarycenter (K := ℝ) (A i) (hA i)) q)
      (((n : ℝ)/((n : ℝ) + 1)) * d) := by
    intro i j
    rcases le_total i j with hij | hij
    · refine le_trans (subBarycenter_dist_le q d hq (hA i) (hA j) (hmono i j hij)) ?_
      refine le_trans (mul_le_mul_of_nonneg_right
        (hfrac (A j).card (Finset.card_pos.mpr (hA j)) (by
          simpa using Finset.card_le_card (Finset.subset_univ (A j)))) hd0) ?_
      rw [mul_comm ((n : ℝ)/((n : ℝ) + 1)) d]
    · rw [dist_comm]
      refine le_trans (subBarycenter_dist_le q d hq (hA j) (hA i) (hmono j i hij)) ?_
      refine le_trans (mul_le_mul_of_nonneg_right
        (hfrac (A i).card (Finset.card_pos.mpr (hA i)) (by
          simpa using Finset.card_le_card (Finset.subset_univ (A i)))) hd0) ?_
      rw [mul_comm ((n : ℝ)/((n : ℝ) + 1)) d]
  rw [hr']
  exact hmain

/-- `meshSpan` is monotone in the mesh bound. -/
lemma esc_meshSpan_mono {m l : ℕ} {d d' : ℝ} (h : d ≤ d') :
    meshSpan m l d ≤ meshSpan m l d' := by
  rw [meshSpan, meshSpan]
  refine Submodule.span_mono ?_
  rintro _ ⟨q, rfl⟩
  exact ⟨⟨q.1, fun i j => le_trans (q.2 i j) h⟩, rfl⟩

/-- The span of the subdivision simplices is contained in the span of the `1`-close ones. -/
lemma esc_tupSpan_le_meshSpan_one (m l : ℕ) : tupSpan m l ≤ meshSpan m l 1 := by
  rw [tupSpan, meshSpan]
  refine Submodule.span_mono ?_
  rintro _ ⟨q, rfl⟩
  exact ⟨⟨q.1, esc_vclose_one q.1⟩, rfl⟩

/-- **One subdivision step shrinks the mesh by the factor `n/(n+1)`.** The subdivision of a chain
which is a combination of `d`-close affine simplices of `Δ^n` is a combination of
`(n/(n+1)) · d`-close affine simplices. -/
lemma esc_sddeg_meshSpan_le (n : ℕ) (d : ℝ) :
    Submodule.map (sddeg (tSplx n) n).hom (meshSpan n n d) ≤
      meshSpan n n (((n : ℝ)/((n : ℝ) + 1)) * d) := by
  rw [meshSpan, Submodule.map_span]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, ⟨q, rfl⟩, rfl⟩
  dsimp only
  change sddeg (tSplx n) n (gen (tSplx n) n (affineSimplex q.1)) ∈
    meshSpan n n (((n : ℝ)/((n : ℝ) + 1)) * d)
  rw [sddeg_gen]
  have hle : tupSpan n n ≤ Submodule.comap
      (((Submission.Blueprint.singC).map (TopCat.ofHom (affineSimplex q.1))).f n).hom
      (meshSpan n n (((n : ℝ)/((n : ℝ) + 1)) * d)) := by
    rw [tupSpan]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨s, rfl⟩
    change ((Submission.Blueprint.singC).map (TopCat.ofHom (affineSimplex q.1))).f n
        (gen (tSplx n) n (affineSimplex s.1)) ∈ meshSpan n n (((n : ℝ)/((n : ℝ) + 1)) * d)
    have hgm := gen_map (X := tSplx n) (Y := tSplx n) (n := n)
      (f := TopCat.ofHom (affineSimplex q.1)) (σ := affineSimplex s.1)
    have hcomp : (TopCat.Hom.hom (TopCat.ofHom (affineSimplex q.1))).comp (affineSimplex s.1)
        = affineSimplex (fun i => affineSimplex q.1 (s.1 i)) := affineSimplex_comp q.1 s.1
    have key : ((Submission.Blueprint.singC).map (TopCat.ofHom (affineSimplex q.1))).f n
        (gen (tSplx n) n (affineSimplex s.1))
        = gen (tSplx n) n (affineSimplex (fun i => affineSimplex q.1 (s.1 i))) :=
      hgm.trans (congrArg (gen (tSplx n) n) hcomp)
    rw [key]
    exact Submodule.subset_span
      ⟨⟨fun i => affineSimplex q.1 (s.1 i), esc_vclose_affineSimplex_comp q.2 s.2⟩, rfl⟩
  exact hle (esc_sd_mem_tupSpan n)

/-- **The mesh of the iterated subdivision shrinks as expected**: the `k`-fold subdivision of the
fundamental `n`-simplex is a combination of `((n/(n+1))^k)`-close affine `n`-simplices of `Δ^n`. -/
lemma esc_sdIter_mem_meshSpan (n k : ℕ) :
    sdIter n k ∈ meshSpan n n (((n : ℝ)/((n : ℝ) + 1))^k) := by
  induction k with
  | zero => exact esc_tupSpan_le_meshSpan_one n n (esc_sd_mem_tupSpan n)
  | succ k ih =>
      have hsucc : (⇑(sddeg (tSplx n) n))^[k+1] (Sd n) =
          sddeg (tSplx n) n ((⇑(sddeg (tSplx n) n))^[k] (Sd n)) :=
        Function.iterate_succ_apply' (f := ⇑(sddeg (tSplx n) n)) k (Sd n)
      have hsd : sdIter n (k+1) = sddeg (tSplx n) n (sdIter n k) := hsucc
      rw [hsd, pow_succ']
      exact esc_sddeg_meshSpan_le n (((n : ℝ)/((n : ℝ) + 1))^k) (Submodule.mem_map_of_mem ih)

/-! ## Pushing small simplices into the submodule of small chains -/

/-- If every `d`-close affine simplex of `Δ^n` yields, after composing with `σ`, a `(U,V)`-small
generator, then pushing a `d`-close chain forward along `σ` gives a `(U,V)`-small chain. -/
lemma esc_map_meshSpan_le_smallChain (X : TopCat) (U V : Set X) (n : ℕ) (σ : singMap X n)
    (d : ℝ)
    (hd : ∀ q : Fin (n+1) → StdSimplex ℝ (Fin (n+1)), VClose q d →
      gen X n (σ.comp (affineSimplex q)) ∈ smallChain X n U V) :
    Submodule.map (((Submission.Blueprint.singC).map (TopCat.ofHom σ)).f n).hom
      (meshSpan n n d) ≤ smallChain X n U V := by
  rw [meshSpan, Submodule.map_span]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, ⟨q, rfl⟩, rfl⟩
  dsimp only
  rw [gen_map (X := tSplx n) (Y := X) (n := n) (f := TopCat.ofHom σ)
    (σ := affineSimplex q.1)]
  exact hd q.1 q.2

/-! ## Linearity of the iterated subdivision -/

/-- The iterated barycentric subdivision is additive. -/
lemma esc_iter_add (X : TopCat) (n K : ℕ) (x y : ((Submission.Blueprint.singC).obj X).X n) :
    (sddeg X n)^[K] (x + y) = (sddeg X n)^[K] x + (sddeg X n)^[K] y := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [show (⇑(sddeg X n))^[K+1] (x + y) =
            (sddeg X n) ((⇑(sddeg X n))^[K] (x + y)) from
          Function.iterate_succ_apply' (f := ⇑(sddeg X n)) K (x + y),
        show (⇑(sddeg X n))^[K+1] x =
            (sddeg X n) ((⇑(sddeg X n))^[K] x) from
          Function.iterate_succ_apply' (f := ⇑(sddeg X n)) K x,
        show (⇑(sddeg X n))^[K+1] y =
            (sddeg X n) ((⇑(sddeg X n))^[K] y) from
          Function.iterate_succ_apply' (f := ⇑(sddeg X n)) K y,
        ih, map_add]

/-- The iterated barycentric subdivision is `ℤ`-linear. -/
lemma esc_iter_smul (X : TopCat) (n K : ℕ) (a : ℤ)
    (x : ((Submission.Blueprint.singC).obj X).X n) :
    (sddeg X n)^[K] (a • x) = a • (sddeg X n)^[K] x := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [show (⇑(sddeg X n))^[K+1] (a • x) =
            (sddeg X n) ((⇑(sddeg X n))^[K] (a • x)) from
          Function.iterate_succ_apply' (f := ⇑(sddeg X n)) K (a • x),
        show (⇑(sddeg X n))^[K+1] x =
            (sddeg X n) ((⇑(sddeg X n))^[K] x) from
          Function.iterate_succ_apply' (f := ⇑(sddeg X n)) K x,
        ih, map_zsmul]

/-- The iterated barycentric subdivision kills `0`. -/
lemma esc_iter_zero (X : TopCat) (n K : ℕ) :
    (sddeg X n)^[K] (0 : ((Submission.Blueprint.singC).obj X).X n) = 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [show (⇑(sddeg X n))^[K+1] (0 : ((Submission.Blueprint.singC).obj X).X n) =
            (sddeg X n) ((⇑(sddeg X n))^[K] (0 : ((Submission.Blueprint.singC).obj X).X n)) from
          Function.iterate_succ_apply' (f := ⇑(sddeg X n)) K 0,
        ih, map_zero]

/-- **The subdivision of a generator.** The `(k+1)`-fold subdivision of the generator of a
singular simplex is the pushforward of the `k`-fold subdivision of the fundamental simplex along
that simplex. -/
lemma esc_sddeg_iter_gen (X : TopCat) (n : ℕ) (σ : singMap X n) (k : ℕ) :
    (sddeg X n)^[k+1] (gen X n σ) =
      ((Submission.Blueprint.singC).map (TopCat.ofHom σ)).f n (sdIter n k) := by
  induction k with
  | zero =>
      rw [Function.iterate_one, sddeg_gen]
      rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih,
        ← sddeg_naturality (tSplx n) X (TopCat.ofHom σ) n (sdIter n k)]
      congr 1
      exact (Function.iterate_succ_apply' (sddeg (tSplx n) n) k (Sd n)).symm

/-- **Iterates of the subdivision as powers of the associated linear map.** -/
lemma esc_pow_apply (X : TopCat) (n K : ℕ) (x : ((Submission.Blueprint.singC).obj X).X n) :
    ((sddeg X n).hom ^ K) x = (sddeg X n)^[K] x := by
  rw [Module.End.pow_apply]

/-! ## The ratio `n/(n+1)` and the Lebesgue step -/

/-- Powers of `n/(n+1)` are eventually below any positive real number. -/
lemma esc_exists_pow_le (n : ℕ) {d : ℝ} (hd : 0 < d) :
    ∃ k : ℕ, ∀ K ≥ k, ((n : ℝ)/((n : ℝ) + 1))^K ≤ d := by
  by_cases hn : n = 0
  · subst hn
    refine ⟨1, fun K hK => ?_⟩
    have hK0 : K ≠ 0 := by omega
    have hz : (((0 : ℕ) : ℝ) / (((0 : ℕ) : ℝ) + 1)) = 0 := by norm_num
    rw [hz, zero_pow hK0]
    exact le_of_lt hd
  · have h0 : 0 ≤ (n : ℝ)/((n : ℝ) + 1) := by positivity
    have h1 : (n : ℝ)/((n : ℝ) + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hd h1
    exact ⟨k, fun K hK => le_trans (pow_le_pow_of_le_one h0 (le_of_lt h1) hK) (le_of_lt hk)⟩

/-- **Every generator becomes small after enough subdivisions.** -/
lemma esc_gen_eventually_small (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (n : ℕ) (σ : singMap X n) :
    ∃ k : ℕ, ∀ K ≥ k, ((sddeg X n).hom ^ K) (gen X n σ) ∈ smallChain X n U V := by
  obtain ⟨d, hdpos, hd⟩ := exists_delta_small X U V hU hV hUV n σ
  obtain ⟨k₀, hk₀⟩ := esc_exists_pow_le n hdpos
  refine ⟨k₀ + 1, fun K hK => ?_⟩
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hK' : k₀ ≤ K' := by omega
  rw [show ((sddeg X n).hom ^ (K' + 1)) (gen X n σ) = (sddeg X n)^[K' + 1] (gen X n σ) from
    esc_pow_apply X n (K' + 1) (gen X n σ)]
  rw [esc_sddeg_iter_gen X n σ K']
  exact esc_map_meshSpan_le_smallChain X U V n σ d hd
    (Submodule.mem_map_of_mem (esc_meshSpan_mono (hk₀ K' hK') (esc_sdIter_mem_meshSpan n K')))

/-! ## The main result -/

/-- **Every chain becomes small after enough barycentric subdivisions.** -/
theorem exists_small_chain (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (n : ℕ) (z : ((Submission.Blueprint.singC).obj X).X n) :
    ∃ k : ℕ, (Work.SingMV.sddeg X n)^[k] z ∈ Work.SingMV.smallChain X n U V := by
  classical
  -- The submodule of chains that are small after *every* sufficiently large number of
  -- subdivisions.
  let W : Submodule ℤ (((Submission.Blueprint.singC).obj X).X n) :=
    { carrier := {w | ∃ k : ℕ, ∀ K ≥ k, ((sddeg X n).hom ^ K) w ∈ smallChain X n U V}
      zero_mem' := ⟨0, fun K _ => by
        rw [map_zero]
        exact Submodule.zero_mem _⟩
      add_mem' := fun {x y} hx hy => by
        obtain ⟨kx, hx⟩ := hx
        obtain ⟨ky, hy⟩ := hy
        refine ⟨max kx ky, fun K hK => ?_⟩
        rw [LinearMap.map_add]
        exact Submodule.add_mem _
          (hx K (le_of_max_le_left hK)) (hy K (le_of_max_le_right hK))
      smul_mem' := fun (a : ℤ) {x} hx => by
        obtain ⟨kx, hx⟩ := hx
        refine ⟨kx, fun K hK => ?_⟩
        rw [LinearMap.map_smul]
        exact Submodule.smul_mem (smallChain X n U V) a (hx K hK) }
  have hgen : ∀ σ : singMap X n, gen X n σ ∈ W :=
    fun σ => esc_gen_eventually_small X U V hU hV hUV n σ
  -- `z` is a finite linear combination of generators.
  have hdecomp : z ∈ Submodule.span ℤ (Set.range (gen X n)) := by
    set f : singMap X n →₀ ℤ := SmallSpanAux.eLin X n z with hf
    have hde : (SmallSpanAux.eLin X n) (∑ σ ∈ f.support, (f σ) • gen X n σ) = f := by
      rw [map_sum]
      have h2 : (∑ σ ∈ f.support, (SmallSpanAux.eLin X n) ((f σ) • gen X n σ))
          = ∑ σ ∈ f.support, Finsupp.single σ (f σ) :=
        Finset.sum_congr rfl fun σ _ => by
          rw [map_zsmul, SmallSpanAux.eLin_gen, Finsupp.smul_single]
          simp
      rw [h2]
      exact Finsupp.sum_single f
    have hz : (∑ σ ∈ f.support, (f σ) • gen X n σ) = z :=
      (SmallSpanAux.eLin X n).injective (by rw [hde, hf])
    rw [← hz]
    exact (Submodule.span ℤ (Set.range (gen X n))).sum_mem
      fun σ _ => smul_mem_int (Submodule.subset_span (Set.mem_range_self σ)) (f σ)
  have hmem : z ∈ W := by
    have hle : Submodule.span ℤ (Set.range (gen X n)) ≤ W :=
      Submodule.span_le.mpr fun x hx => by
        obtain ⟨σ, rfl⟩ := hx
        exact hgen σ
    exact hle hdecomp
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, ?_⟩
  rw [← esc_pow_apply X n k z]
  exact hk k le_rfl

end Work.SingMV

import Mathlib
import Submission.Work.SINGMV.Defs
import Submission.Work.SingMV.SdAux
import Submission.Work.SingMV.Bdry_mem_affineSpan
import Submission.Work.SingMV.sddeg_aux
import Submission.Work.SingMV.phi_comp_phi

/-!
# The boundary of the barycentric subdivision of the fundamental simplex

`Work.SingMV.sddeg_d` needs the identity `∂ (Sd (n+1)) = Bdry n` (the statement also known in
this workspace as `Work.SingMV.Sd_d`) together with the values of `sddeg` on generators.  This
file proves that identity from scratch (the lemmas are suffixed `_aux` to leave the names
`Sd_d`, `coneBoundary` free for the modules in which colleagues are developing the same result):

* `smul_id_apply_sd`: applying a scalar multiple of the identity linear map;
* `coneFace_castSucc`, `coneFace_last`: the faces of the cone over an affine simplex;
* `coneGen_aux` and `coneBoundary_aux`: the cone boundary formula
  `∂ (cone z) = (-1)^{deg z + 1} z + cone (∂ z)` for chains of affine simplices;
* `genId_mem_affineSpan`, `genId_d`: the fundamental `1`-simplex and its boundary;
* `Bdry_cycle_aux`: the subdivided boundary is a cycle (given `Sd_d` one degree down);
* `Sd_d_aux`: `∂ (Sd (n+1)) = Bdry n` by induction, with the degree `0` case handled by
  expressing the cone on `Bdry 0` as the difference of `∂ (cone (gen id))` and `gen id`.
-/

open CategoryTheory Limits Convexity
open scoped BigOperators Simplicial
noncomputable section
namespace Work.SingMV

/-- Applying a scalar multiple of the identity linear map. -/
lemma smul_id_apply_sd {M : Type*} [AddCommGroup M] [Module ℤ M] (c : ℤ) (y : M) :
    (c • (LinearMap.id : M →ₗ[ℤ] M)) y = c • y := by
  simp

theorem coneFace_castSucc {N k : ℕ} (q : Fin (k+2) → StdSimplex ℝ (Fin (N+1)))
    (b : StdSimplex ℝ (Fin (N+1))) (i : Fin (k+2)) (j : Fin (k+2)) :
    (Fin.snoc (α := fun _ => StdSimplex ℝ (Fin (N+1))) q b) (i.castSucc.succAbove j) =
      (Fin.snoc (α := fun _ => StdSimplex ℝ (Fin (N+1)))
        (fun j : Fin (k+1) => q (i.succAbove j)) b) j := by
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rw [Fin.castSucc_succAbove_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Fin.succAbove_castSucc_of_le _ _ (Fin.le_last i)]
    show (Fin.snoc (α := fun _ => StdSimplex ℝ (Fin (N+1))) q b) (Fin.last (k+2)) =
      (Fin.snoc (α := fun _ => StdSimplex ℝ (Fin (N+1)))
        (fun j : Fin (k+1) => q (i.succAbove j)) b) (Fin.last (k+1))
    rw [Fin.snoc_last, Fin.snoc_last]

theorem coneFace_last {N k : ℕ} (q : Fin (k+2) → StdSimplex ℝ (Fin (N+1)))
    (b : StdSimplex ℝ (Fin (N+1))) (j : Fin (k+2)) :
    (Fin.snoc (α := fun _ => StdSimplex ℝ (Fin (N+1))) q b)
      ((Fin.last (k+2)).succAbove j) = q j := by
  rw [Fin.succAbove_last, Fin.snoc_castSucc]

theorem coneGen_aux (N k : ℕ) (b : StdSimplex ℝ (Fin (N+1)))
    (q : Fin (k+2) → StdSimplex ℝ (Fin (N+1))) :
    (((Submission.Blueprint.singC).obj (tSplx N)).d (k+2) (k+1))
        (coneChain N b (k+1) (gen (tSplx N) (k+1) (affineSimplex q))) =
      (-1 : ℤ) ^ (k+2) • gen (tSplx N) (k+1) (affineSimplex q)
        + coneChain N b k ((((Submission.Blueprint.singC).obj (tSplx N)).d (k+1) k)
            (gen (tSplx N) (k+1) (affineSimplex q))) := by
  have E1 : coneChain N b (k+1) (gen (tSplx N) (k+1) (affineSimplex q)) =
      gen (tSplx N) (k+2) (affineSimplex (n := N) (k := k+2) (Fin.snoc q b)) := by
    rw [coneChain_gen N (k+1) b (affineSimplex (n := N) (k := k+1) q)]
    rw [show (fun i : Fin (k+2) =>
        affineSimplex (n := N) (k := k+1) q (vert (k+2) i)) = q from
      funext fun i => affineSimplex_vert q i]
  have T1 : ∀ i : Fin (k+2),
      (affineSimplex (n := N) (k := k+2) (Fin.snoc q b)).comp
          ((coface (k+1) i.castSucc).hom) =
        affineSimplex (n := N) (k := k+1)
          (Fin.snoc (fun j : Fin (k+1) => q (i.succAbove j)) b) := by
    intro i
    rw [affineSimplex_coface]
    congr 1
    funext j
    exact coneFace_castSucc q b i j
  have T2 : (affineSimplex (n := N) (k := k+2) (Fin.snoc q b)).comp
        ((coface (k+1) (Fin.last (k+2))).hom) = affineSimplex (n := N) (k := k+1) q := by
    rw [affineSimplex_coface]
    congr 1
    funext j
    exact coneFace_last q b j
  have T3 : ∀ i : Fin (k+2),
      coneChain N b k (gen (tSplx N) k (affineSimplex (n := N) (k := k)
          (fun j : Fin (k+1) => q (i.succAbove j)))) =
        gen (tSplx N) (k+1) (affineSimplex (n := N) (k := k+1)
          (Fin.snoc (fun j : Fin (k+1) => q (i.succAbove j)) b)) := by
    intro i
    rw [coneChain_gen N k b (affineSimplex (n := N) (k := k)
      (fun j : Fin (k+1) => q (i.succAbove j)))]
    rw [show (fun i' : Fin (k+1) =>
        affineSimplex (n := N) (k := k) (fun j : Fin (k+1) => q (i.succAbove j))
          (vert (k+1) i')) = (fun j : Fin (k+1) => q (i.succAbove j)) from
      funext fun i' => affineSimplex_vert _ i']
  rw [E1, gen_d_sd (tSplx N) (k+1) (affineSimplex (n := N) (k := k+2) (Fin.snoc q b))]
  rw [Fin.sum_univ_castSucc]
  rw [gen_d_sd (tSplx N) k (affineSimplex (n := N) (k := k+1) q), map_sum]
  simp only [map_zsmul]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin (k+2)))) =>
    congrArg (fun w => (-1 : ℤ) ^ (i.castSucc : ℕ) • gen (tSplx N) (k+1) w) (T1 i))]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin (k+2)))) =>
    congrArg (fun w => (-1 : ℤ) ^ (i : ℕ) • coneChain N b k (gen (tSplx N) k w))
      (affineSimplex_coface q i))]
  rw [T2]
  simp only [Fin.val_castSucc, Fin.val_last, T3]
  abel

theorem coneBoundary_aux (N k : ℕ) (b : StdSimplex ℝ (Fin (N+1)))
    (z : ((Submission.Blueprint.singC).obj (tSplx N)).X (k+1))
    (hz : z ∈ affineSpan N (k+1)) :
    (((Submission.Blueprint.singC).obj (tSplx N)).d (k+2) (k+1)) (coneChain N b (k+1) z) =
      (-1 : ℤ) ^ (k+2) • z + coneChain N b k
        ((((Submission.Blueprint.singC).obj (tSplx N)).d (k+1) k) z) := by
  have key : ∀ x ∈ affineSpan N (k+1),
      (((Submission.Blueprint.singC).obj (tSplx N)).d (k+2) (k+1)) (coneChain N b (k+1) x) =
        (-1 : ℤ) ^ (k+2) • x + coneChain N b k
          ((((Submission.Blueprint.singC).obj (tSplx N)).d (k+1) k) x) := by
    intro x hx
    set A : ((Submission.Blueprint.singC).obj (tSplx N)).X (k+1) →ₗ[ℤ]
        ((Submission.Blueprint.singC).obj (tSplx N)).X (k+1) :=
      (((Submission.Blueprint.singC).obj (tSplx N)).d (k+2) (k+1)).hom.comp
        (coneChain N b (k+1)).hom with hA
    set B : ((Submission.Blueprint.singC).obj (tSplx N)).X (k+1) →ₗ[ℤ]
        ((Submission.Blueprint.singC).obj (tSplx N)).X (k+1) :=
      (coneChain N b k).hom.comp
        (((Submission.Blueprint.singC).obj (tSplx N)).d (k+1) k).hom with hB
    have hle : affineSpan N (k+1) ≤
        LinearMap.ker (A - B - ((-1 : ℤ) ^ (k+2)) • LinearMap.id) := by
      rw [affineSpan, Submodule.span_le]
      rintro _ ⟨q, rfl⟩
      refine LinearMap.mem_ker.mpr ?_
      rw [hA, hB]
      simp only [LinearMap.sub_apply, LinearMap.comp_apply]
      rw [coneGen_aux N k b q, smul_id_apply_sd]
      abel
    have h1 : (A - B - ((-1 : ℤ) ^ (k+2)) • (LinearMap.id : ((Submission.Blueprint.singC).obj
        (tSplx N)).X (k+1) →ₗ[ℤ] ((Submission.Blueprint.singC).obj (tSplx N)).X (k+1))) x = 0 :=
      LinearMap.mem_ker.mp (hle hx)
    simp only [LinearMap.sub_apply] at h1
    rw [smul_id_apply_sd] at h1
    have h2 : A x - B x = (-1 : ℤ) ^ (k+2) • x := sub_eq_zero.mp h1
    rw [sub_eq_iff_eq_add] at h2
    rw [hA, hB] at h2
    simpa only [LinearMap.comp_apply] using h2
  exact key z hz

/-- The fundamental `1`-simplex is an affine simplex. -/
lemma genId_mem_affineSpan :
    gen (tSplx 1) 1 (ContinuousMap.id (StdSimplex ℝ (Fin 2))) ∈ affineSpan 1 1 := by
  have h : gen (tSplx 1) 1 (ContinuousMap.id (StdSimplex ℝ (Fin 2)))
      = gen (tSplx 1) 1 (affineSimplex (n := 1) (k := 1) (fun i : Fin 2 => vert 2 i)) := by
    congr 1
    exact (affineSimplex_eq_id 1).symm
  rw [h]
  exact Submodule.subset_span ⟨(fun i : Fin 2 => vert 2 i), rfl⟩

/-- The boundary of the fundamental `1`-simplex is `Bdry 0`. -/
lemma genId_d :
    (((Submission.Blueprint.singC).obj (tSplx 1)).d 1 0)
        (gen (tSplx 1) 1 (ContinuousMap.id (StdSimplex ℝ (Fin 2)))) = Bdry 0 := by
  rw [gen_d_sd (tSplx 1) 0 (ContinuousMap.id (StdSimplex ℝ (Fin 2)))]
  rw [show Bdry 0 = SdBdry 0 (Sd 0) from (SdBdry_eq_phi 0 (Sd 0)).symm]
  simp only [SdBdry]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show Sd 0 = gen (tSplx 0) 0 (ContinuousMap.id (StdSimplex ℝ (Fin (0+1)))) from rfl,
    gen_map]
  simp

/-- The subdivided boundary is a cycle, given `Sd_d` at the previous index. -/
lemma Bdry_cycle_aux (N : ℕ)
    (h : (((Submission.Blueprint.singC).obj (tSplx (N+1))).d (N+1) N)
        (Sd (N+1)) = Bdry N) :
    (((Submission.Blueprint.singC).obj (tSplx (N+2))).d (N+1) N)
        (Bdry (N+1)) = 0 := by
  have hcomm : (((Submission.Blueprint.singC).obj (tSplx (N+2))).d (N+1) N)
        ((phi (N+1)).f (N+1) (Sd (N+1)))
      = (phi (N+1)).f N ((((Submission.Blueprint.singC).obj (tSplx (N+1))).d (N+1) N)
          (Sd (N+1))) :=
    congrArg (fun m => m (Sd (N+1))) (HomologicalComplex.Hom.comm (phi (N+1)) (N+1) N)
  show (((Submission.Blueprint.singC).obj (tSplx (N+2))).d (N+1) N) (Bdry (N+1)) = 0
  rw [show Bdry (N+1) = (phi (N+1)).f (N+1) (Sd (N+1)) from rfl, hcomm, h,
    show Bdry N = (phi N).f N (Sd N) from rfl]
  rw [← CategoryTheory.comp_apply, ← HomologicalComplex.comp_f, phi_comp_phi N,
    HomologicalComplex.zero_f]
  rfl

/-- **The boundary of the barycentric subdivision of the fundamental simplex.** -/
theorem Sd_d_aux (n : ℕ) :
    (((Submission.Blueprint.singC).obj (tSplx (n+1))).d (n+1) n)
        (Sd (n+1)) = Bdry n := by
  induction n with
  | zero =>
    have hsd : Sd 1 = (-1 : ℤ) ^ 1 • coneChain 1
        (unif (Finset.univ : Finset (Fin (0+2))) Finset.univ_nonempty) 0 (Bdry 0) := by
      rw [show Sd (0+1) = (-1 : ℤ) ^ (0+1) • coneChain (0+1)
          (unif (Finset.univ : Finset (Fin (0+2))) Finset.univ_nonempty) 0
          (SdBdry 0 (Sd 0)) from rfl]
      rw [show SdBdry 0 (Sd 0) = Bdry 0 from SdBdry_eq_phi 0 (Sd 0)]
    have hcone := coneBoundary_aux 1 0
      (unif (Finset.univ : Finset (Fin (0+2))) Finset.univ_nonempty)
      (gen (tSplx 1) 1 (ContinuousMap.id (StdSimplex ℝ (Fin 2)))) genId_mem_affineSpan
    have hcone' : (((Submission.Blueprint.singC).obj (tSplx 1)).d 2 1)
          (coneChain 1 (unif (Finset.univ : Finset (Fin (0+2))) Finset.univ_nonempty) 1
            (gen (tSplx 1) 1 (ContinuousMap.id (StdSimplex ℝ (Fin 2)))))
        = gen (tSplx 1) 1 (ContinuousMap.id (StdSimplex ℝ (Fin 2)))
          + coneChain 1 (unif (Finset.univ : Finset (Fin (0+2))) Finset.univ_nonempty) 0
              (Bdry 0) := by
      rw [hcone, genId_d]
      norm_num
    have hsub : coneChain 1 (unif (Finset.univ : Finset (Fin (0+2))) Finset.univ_nonempty) 0
          (Bdry 0)
        = (((Submission.Blueprint.singC).obj (tSplx 1)).d 2 1)
            (coneChain 1 (unif (Finset.univ : Finset (Fin (0+2))) Finset.univ_nonempty) 1
              (gen (tSplx 1) 1 (ContinuousMap.id (StdSimplex ℝ (Fin 2)))))
          - gen (tSplx 1) 1 (ContinuousMap.id (StdSimplex ℝ (Fin 2))) := by
      rw [hcone']
      abel
    have hdd : (((Submission.Blueprint.singC).obj (tSplx 1)).d 1 0)
          ((((Submission.Blueprint.singC).obj (tSplx 1)).d 2 1)
            (coneChain 1 (unif (Finset.univ : Finset (Fin (0+2))) Finset.univ_nonempty) 1
              (gen (tSplx 1) 1 (ContinuousMap.id (StdSimplex ℝ (Fin 2)))))) = 0 := by
      rw [← CategoryTheory.comp_apply, HomologicalComplex.d_comp_d]
      simp
    have hfinal : (((Submission.Blueprint.singC).obj (tSplx 1)).d 1 0)
          (coneChain 1 (unif (Finset.univ : Finset (Fin (0+2))) Finset.univ_nonempty) 0
            (Bdry 0)) = - Bdry 0 := by
      rw [hsub, map_sub, hdd, genId_d]
      simp
    rw [hsd, map_zsmul, hfinal]
    simp
  | succ n ih =>
    have hsd : Sd (n+2) = (-1 : ℤ) ^ (n+2) • coneChain (n+2)
        (unif (Finset.univ : Finset (Fin (n+2+1))) Finset.univ_nonempty) (n+1) (Bdry (n+1)) := by
      rw [show Sd ((n+1)+1) = (-1 : ℤ) ^ ((n+1)+1) • coneChain ((n+1)+1)
          (unif (Finset.univ : Finset (Fin ((n+1)+1+1))) Finset.univ_nonempty) (n+1)
          (SdBdry (n+1) (Sd (n+1))) from rfl]
      rw [show SdBdry (n+1) (Sd (n+1)) = Bdry (n+1) from SdBdry_eq_phi (n+1) (Sd (n+1))]
    have hcone := coneBoundary_aux (n+2) n
      (unif (Finset.univ : Finset (Fin (n+2+1))) Finset.univ_nonempty)
      (Bdry (n+1)) (Bdry_mem_affineSpan (n+1))
    have hcycle : (((Submission.Blueprint.singC).obj (tSplx (n+2))).d (n+1) n)
        (Bdry (n+1)) = 0 := Bdry_cycle_aux n ih
    rw [hsd, map_zsmul, hcone, hcycle, map_zero, add_zero]
    have hcoe : ((-1 : ℤ) ^ (n+2)) * ((-1 : ℤ) ^ (n+2)) = 1 := by
      rw [← mul_pow]
      norm_num
    rw [← mul_zsmul, hcoe]
    simp

end Work.SingMV

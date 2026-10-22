import Mathlib
import Submission.Work.SINGMV.Defs
import Submission.Work.SingMV.gen_d
import Submission.Work.SingMV.sddeg_naturality
import Submission.Work.SingMV.sddeg_aux
import Submission.Work.SingMV.SdAux
import Submission.Work.SingMV.Bdry_mem_affineSpan
import Submission.Work.SingMV.exists_finsupp_equiv

/-!
# The chain homotopy `∂ H + H ∂ = Sd - id` for the barycentric subdivision

The degreewise homotopy operator `homdeg X n : C_n(X) ⟶ C_{n+1}(X)` is the pushforward of the
universal homotopy chain `homChain n ∈ C_{n+1}(Δⁿ)` along a singular simplex.  This file proves
the chain homotopy identity

  `d (homdeg X (n+1) z) + homdeg X n (d z) = sddeg X (n+1) z - z`   for `z ∈ C_{n+1}(X)`,

i.e. that `sddeg` is chain homotopic to the identity (which is what makes the barycentric
subdivision a quasi-isomorphism).

## Route

Everything happens on the fundamental simplex first.  Write `e n = gen (Δⁿ) n (id)` for the
identity simplex and `a n := Sd n - e n - phiF (n-1) n (homChain (n-1))` (the cycle which the
recursion cones).  The key input is `homChain_rec` :

  `d (homChain (n+1)) = Sd (n+1) - e (n+1) - phiF n (n+1) (homChain n)`   (`≈ ∂ H = Sd - id`),

proved by induction using the cone boundary formula `coneBoundaryF`
(`∂ (cone z) = (-1)^{k+2} z + cone (∂ z)` for `z` in the span of the affine simplices),
`Sd_d_final` (`∂ (Sd (n+1)) = Bdry n`) and `phi_comp_phi_sd` (`Φ² = 0`).
Transporting along a simplex `σ : Δⁿ ⟶ X` and using linearity in the space gives the theorem.
-/

open CategoryTheory Limits Convexity
open scoped BigOperators Simplicial

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.SingMV

/-- The singular `k`-chains of `Δ^N`. -/
abbrev chN (N k : ℕ) : Type := ↥(((Submission.Blueprint.singC).obj (tSplx N)).X k)

/-- The singular `n`-chains of a space `X`. -/
abbrev chX (X : TopCat) (n : ℕ) : Type := ↥(((Submission.Blueprint.singC).obj X).X n)

/-- The generator of the fundamental `n`-chain of `Δⁿ` (the identity simplex). -/
abbrev eGen (n : ℕ) : ((Submission.Blueprint.singC).obj (tSplx n)).X n :=
  gen (tSplx n) n (ContinuousMap.id _)

/-- `(phi n).f k` is the alternating sum of the pushforwards along the cofaces, in degree `k`. -/
lemma phi_f_eq (n k : ℕ) :
    (phi n).f k = ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) •
        ((Submission.Blueprint.singC).map (coface n i)).f k := by
  rw [phi, chainComplex_sum_f]
  exact Finset.sum_congr rfl (fun i _ => HomologicalComplex.zsmul_f_apply _ _ _)

/-- The value of `phi` on a chain, as an alternating sum. -/
lemma phi_apply_sum (n k : ℕ) (y : chN n k) :
    (phi n).f k y = ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) •
        ((Submission.Blueprint.singC).map (coface n i)).f k y := by
  rw [phi_f_eq n k]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_smul, LinearMap.sum_apply, LinearMap.smul_apply]

/-! ## The missing face of a cone

Coning appends the apex as the *last* vertex (`Fin.snoc`).  The two identities below describe
the faces of such a cone: deleting an earlier vertex and deleting the apex. -/

/-- Deleting the vertex `i` from the cone tuple `(q, b)` gives the cone over the `i`-th face of
`q`. -/
lemma snoc_succAbove {k : ℕ} {α : Type*} (q : Fin (k+2) → α) (b : α) (i : Fin (k+2)) :
    (Fin.snoc q b : Fin (k+3) → α) ∘ (i.castSucc).succAbove
      = Fin.snoc (q ∘ i.succAbove) b := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · rw [Function.comp_apply]
    rw [Fin.succAbove_of_le_castSucc (i.castSucc) (Fin.last (k+1))
      (by exact Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i))]
    rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_last]
  · intro j'
    rw [Function.comp_apply]
    rcases lt_or_ge j'.castSucc i with h | h
    · rw [Fin.succAbove_castSucc_of_lt i j'.castSucc h, Fin.snoc_castSucc, Fin.snoc_castSucc]
      congr 1
      exact (Fin.succAbove_of_castSucc_lt i j' (by simpa using h)).symm
    · rw [Fin.succAbove_castSucc_of_le i j'.castSucc h, Fin.succ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_castSucc]
      congr 1
      exact (Fin.succAbove_of_le_castSucc i j' (by simpa using h)).symm

/-- Deleting the apex of a cone gives back the original tuple. -/
lemma snoc_last_succAbove {k : ℕ} {α : Type*} (q : Fin (k+2) → α) (b : α) :
    (Fin.snoc q b : Fin (k+3) → α) ∘ (Fin.last (k+2)).succAbove = q := by
  funext j
  rw [Function.comp_apply, Fin.succAbove_last_apply, Fin.snoc_castSucc]

/-- `ℤ`-linearity of a linear map, with the `ZSMul` instance on both sides. -/
lemma map_smul_int' {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (f : M →ₗ[ℤ] N) (c : ℤ) (x : M) : f (c • x) = c • f x := by
  rw [← int_smul_eq_zsmul (inferInstance : Module ℤ M) c x,
      ← int_smul_eq_zsmul (inferInstance : Module ℤ N) c (f x)]
  exact f.map_smul c x

/-- An affine simplex on a vertex tuple `q` takes the value `q i` at the `i`-th vertex, so the
vertex tuple of `affineSimplex q` is `q` again. -/
lemma snoc_affineSimplex_vert {N k : ℕ} (q : Fin (k+1) → StdSimplex ℝ (Fin (N+1))) :
    (fun j : Fin (k+1) => (affineSimplex (n := N) (k := k) q) (vert (k+1) j)) = q :=
  funext (fun j => affineSimplex_vert q j)

/-- The scalar multiplication by `c` as a linear map is the `ZSMul` multiplication (the two
`ℤ`-actions on a `ℤ`-module agree). -/
lemma lsmul_apply_zsmul {M : Type*} [AddCommGroup M] [Module ℤ M] (c : ℤ) (x : M) :
    (LinearMap.lsmul ℤ M c) x = c • x := by
  rw [LinearMap.lsmul_apply]
  exact int_smul_eq_zsmul (inferInstance : Module ℤ M) c x

/-! ## The boundary of a cone -/

/-- **The boundary of a cone.**  For a chain `z` of `Δ^N` which is a combination of affine
simplices, the boundary of its cone with apex `b` is `(-1)^{k+2} z + cone (∂ z)`. -/
theorem coneBoundaryF (N k : ℕ) (b : StdSimplex ℝ (Fin (N+1)))
    (z : ((Submission.Blueprint.singC).obj (tSplx N)).X (k+1))
    (hz : z ∈ affineSpan N (k+1)) :
    (((Submission.Blueprint.singC).obj (tSplx N)).d (k+2) (k+1)) (coneChain N b (k+1) z) =
      (-1 : ℤ) ^ (k+2) • z + coneChain N b k
        ((((Submission.Blueprint.singC).obj (tSplx N)).d (k+1) k) z) := by
  -- `L` is the left hand side as a linear map, `R` the right hand side without the constraint
  -- that the two summands be written in the stated order.
  let L : chN N (k+1) →ₗ[ℤ] chN N (k+1) :=
    (((Submission.Blueprint.singC).obj (tSplx N)).d (k+2) (k+1)).hom.comp
      (coneChain N b (k+1)).hom
  let R : chN N (k+1) →ₗ[ℤ] chN N (k+1) :=
    (coneChain N b k).hom.comp
        (((Submission.Blueprint.singC).obj (tSplx N)).d (k+1) k).hom
      + LinearMap.lsmul ℤ (chN N (k+1)) ((-1 : ℤ) ^ (k+2))
  -- The identity on the affine generators.
  have hgen : ∀ q : Fin (k+2) → StdSimplex ℝ (Fin (N+1)),
      L (gen (tSplx N) (k+1) (affineSimplex q)) =
        R (gen (tSplx N) (k+1) (affineSimplex q)) := by
    intro q
    have hA : (((Submission.Blueprint.singC).obj (tSplx N)).d (k+2) (k+1))
          (coneChain N b (k+1) (gen (tSplx N) (k+1) (affineSimplex q)))
        = ∑ i : Fin (k+3), (-1 : ℤ) ^ (i : ℕ) • gen (tSplx N) (k+1)
            (affineSimplex ((Fin.snoc q b) ∘ i.succAbove)) := by
      rw [coneChain_gen, snoc_affineSimplex_vert, gen_d]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [affineSimplex_coface]
      rfl
    have hB : (coneChain N b k) (((Submission.Blueprint.singC).obj (tSplx N)).d (k+1) k
          (gen (tSplx N) (k+1) (affineSimplex q)))
        = ∑ i : Fin (k+2), (-1 : ℤ) ^ (i : ℕ) • gen (tSplx N) (k+1)
            (affineSimplex (Fin.snoc (q ∘ i.succAbove) b)) := by
      rw [gen_d, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [affineSimplex_coface, map_smul_int', coneChain_gen, snoc_affineSimplex_vert]
      rfl
    simp only [L, R, LinearMap.comp_apply, LinearMap.add_apply]
    change (((Submission.Blueprint.singC).obj (tSplx N)).d (k+2) (k+1))
          (coneChain N b (k+1) (gen (tSplx N) (k+1) (affineSimplex q))) =
        (coneChain N b k) (((Submission.Blueprint.singC).obj (tSplx N)).d (k+1) k
            (gen (tSplx N) (k+1) (affineSimplex q)))
          + LinearMap.lsmul ℤ (chN N (k+1)) ((-1 : ℤ) ^ (k+2))
              (gen (tSplx N) (k+1) (affineSimplex q))
    rw [hA, hB, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, snoc_succAbove, snoc_last_succAbove,
      lsmul_apply_zsmul]
  -- hence everywhere on `affineSpan`, by linearity
  have hle : affineSpan N (k+1) ≤ LinearMap.ker (L - R) := by
    rw [affineSpan, Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    exact LinearMap.mem_ker.mpr (by rw [LinearMap.sub_apply, hgen q, sub_self])
  have hfin : L z = R z := by
    have h := hle hz
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
    exact h
  calc (((Submission.Blueprint.singC).obj (tSplx N)).d (k+2) (k+1)) (coneChain N b (k+1) z)
      = L z := rfl
    _ = R z := hfin
    _ = coneChain N b k ((((Submission.Blueprint.singC).obj (tSplx N)).d (k+1) k) z)
          + (-1 : ℤ) ^ (k+2) • z := by
        simp only [R, LinearMap.add_apply, LinearMap.comp_apply, lsmul_apply_zsmul]
    _ = (-1 : ℤ) ^ (k+2) • z + coneChain N b k
          ((((Submission.Blueprint.singC).obj (tSplx N)).d (k+1) k) z) := add_comm _ _

/-! ## `homChain n` lies in the span of the affine simplices -/

/-- The identity simplex of `Δⁿ` is an affine simplex. -/
lemma eGen_mem_affineSpan (n : ℕ) : eGen n ∈ affineSpan n n := by
  rw [show eGen n = gen (tSplx n) n (affineSimplex (fun i => vert (n+1) i))
      from by rw [affineSimplex_eq_id]]
  exact gen_affineSimplex_mem n n _

/-- The pushforward of an element of `affineSpan` along the coface sum stays in `affineSpan`. -/
lemma phiF_mem_affineSpan (n : ℕ) {z : ((Submission.Blueprint.singC).obj (tSplx n)).X (n+1)}
    (hz : z ∈ affineSpan n (n+1)) : phiF n (n+1) z ∈ affineSpan (n+1) (n+1) := by
  rw [phiF, phi_f_eq n (n+1)]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ (fun i _ => smul_mem_int (coface_mem_affineSpan n (n+1) i hz) _)

/-- `homChain n` is an integral combination of affine `(n+1)`-simplices of `Δⁿ`. -/
theorem homChain_mem_affineSpan' (n : ℕ) : homChain n ∈ affineSpan n (n+1) := by
  induction n with
  | zero =>
    rw [show homChain 0 = 0 from rfl]
    exact Submodule.zero_mem _
  | succ n ih =>
    rw [show homChain (n+1) = (-1 : ℤ) ^ (n+2) • coneChain (n+1)
        (unif (Finset.univ : Finset (Fin (n+2))) Finset.univ_nonempty) (n+1)
        (Sd (n+1) - gen (tSplx (n+1)) (n+1) (ContinuousMap.id _) -
          phiF n (n+1) (homChain n)) from rfl]
    refine smul_mem_int ?_ _
    refine coneChain_mem_affineSpan (n+1) (n+1) _ ?_
    exact Submodule.sub_mem _ (Submodule.sub_mem _ (Sd_mem_affineSpan (n+1))
      (eGen_mem_affineSpan (n+1))) (phiF_mem_affineSpan n ih)

/-- `phi` is compatible with the differential, elementwise. -/
lemma phi_comm_apply' (n : ℕ) (s : chN n n) :
    (((Submission.Blueprint.singC).obj (tSplx (n+1))).d n (n-1)) ((phi n).f n s) =
      (phi n).f (n-1) ((((Submission.Blueprint.singC).obj (tSplx n)).d n (n-1)) s) :=
  congrArg (fun m => m s) (HomologicalComplex.Hom.comm (phi n) n (n-1))

/-- **The boundary of the barycentric subdivision of the fundamental simplex**:
`∂ (Sd (n+1)) = Bdry n`. -/
theorem Sd_d_final (n : ℕ) :
    (((Submission.Blueprint.singC).obj (tSplx (n+1))).d (n+1) n) (Sd (n+1)) = Bdry n := by
  induction n with
  | zero =>
    -- `∂ (Sd 1) = ∂ (- cone (Bdry 0)) = - ∂ (cone (Bdry 0)) = Bdry 0`
    have hgenid : (((Submission.Blueprint.singC).obj (tSplx 1)).d 1 0)
        (gen (tSplx 1) 1 (ContinuousMap.id _)) = Bdry 0 := by
      rw [gen_d, show Bdry 0 = SdBdry 0 (Sd 0) from (SdBdry_eq_phi 0 (Sd 0)).symm,
        show Sd 0 = gen (tSplx 0) 0 (ContinuousMap.id _) from rfl]
      simp only [SdBdry]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [gen_map]
      simp
    have hSd1 : Sd (0+1) = -coneChain (0+1)
        (unif (Finset.univ : Finset (Fin (0+2))) Finset.univ_nonempty) 0 (Bdry 0) := by
      rw [show Sd (0+1) = (-1 : ℤ) ^ (0+1) • coneChain (0+1)
          (unif (Finset.univ : Finset (Fin (0+2))) Finset.univ_nonempty) 0
          (SdBdry 0 (Sd 0)) from rfl,
        show SdBdry 0 (Sd 0) = Bdry 0 from SdBdry_eq_phi 0 (Sd 0)]
      simp
    have hcone := coneBoundaryF 1 0
      (unif (Finset.univ : Finset (Fin (0+2))) Finset.univ_nonempty)
      (gen (tSplx 1) 1 (ContinuousMap.id _)) (eGen_mem_affineSpan 1)
    have hcone' : (((Submission.Blueprint.singC).obj (tSplx 1)).d 2 1)
          (coneChain 1 (unif (Finset.univ : Finset (Fin (0+2))) Finset.univ_nonempty) 1
            (gen (tSplx 1) 1 (ContinuousMap.id _)))
        = gen (tSplx 1) 1 (ContinuousMap.id _)
          + coneChain 1 (unif (Finset.univ : Finset (Fin (0+2))) Finset.univ_nonempty) 0
              (Bdry 0) := by
      rw [hcone, hgenid]
      norm_num
    have hsub : coneChain 1 (unif (Finset.univ : Finset (Fin (0+2))) Finset.univ_nonempty) 0
          (Bdry 0)
        = (((Submission.Blueprint.singC).obj (tSplx 1)).d 2 1)
            (coneChain 1 (unif (Finset.univ : Finset (Fin (0+2))) Finset.univ_nonempty) 1
              (gen (tSplx 1) 1 (ContinuousMap.id _)))
          - gen (tSplx 1) 1 (ContinuousMap.id _) := by
      rw [hcone']
      abel
    have hdd : (((Submission.Blueprint.singC).obj (tSplx 1)).d 1 0)
          ((((Submission.Blueprint.singC).obj (tSplx 1)).d 2 1)
            (coneChain 1 (unif (Finset.univ : Finset (Fin (0+2))) Finset.univ_nonempty) 1
              (gen (tSplx 1) 1 (ContinuousMap.id _)))) = 0 := by
      rw [← CategoryTheory.comp_apply, HomologicalComplex.d_comp_d]
      simp
    have hfinal : (((Submission.Blueprint.singC).obj (tSplx 1)).d 1 0)
          (coneChain 1 (unif (Finset.univ : Finset (Fin (0+2))) Finset.univ_nonempty) 0
            (Bdry 0)) = -Bdry 0 := by
      rw [hsub, map_sub, hdd, hgenid]
      simp
    rw [hSd1, map_neg, hfinal]
    simp
  | succ n ih =>
    have hSd : Sd ((n+1)+1) = (-1 : ℤ) ^ ((n+1)+1) • coneChain ((n+1)+1)
        (unif (Finset.univ : Finset (Fin (((n+1)+1)+1))) Finset.univ_nonempty) (n+1)
        (Bdry (n+1)) := by
      rw [show Sd ((n+1)+1) = (-1 : ℤ) ^ ((n+1)+1) • coneChain ((n+1)+1)
          (unif (Finset.univ : Finset (Fin (((n+1)+1)+1))) Finset.univ_nonempty) (n+1)
          (SdBdry (n+1) (Sd (n+1))) from rfl,
        show SdBdry (n+1) (Sd (n+1)) = Bdry (n+1) from SdBdry_eq_phi (n+1) (Sd (n+1))]
    -- `Bdry (n+1)` is a cycle
    have hcycle : (((Submission.Blueprint.singC).obj (tSplx ((n+1)+1))).d (n+1) n)
        (Bdry (n+1)) = 0 := by
      have h1 : (((Submission.Blueprint.singC).obj (tSplx ((n+1)+1))).d (n+1) n)
          ((phi (n+1)).f (n+1) (Sd (n+1))) = 0 := by
        have hcomm := phi_comm_apply' (n+1) (Sd (n+1))
        rw [show (n+1) - 1 = n from rfl] at hcomm
        rw [hcomm, ih]
        exact (by rw [phi_comp_phi_sd n]; simp :
          ((phi n) ≫ (phi (n+1))).f n (Sd n) = 0)
      exact h1
    have step : (((Submission.Blueprint.singC).obj (tSplx ((n+1)+1))).d ((n+1)+1) (n+1))
          (Sd ((n+1)+1))
        = (-1 : ℤ) ^ ((n+1)+1) •
            (((Submission.Blueprint.singC).obj (tSplx ((n+1)+1))).d ((n+1)+1) (n+1))
              (coneChain ((n+1)+1)
                (unif (Finset.univ : Finset (Fin (((n+1)+1)+1))) Finset.univ_nonempty) (n+1)
                (Bdry (n+1))) := by
      rw [hSd]
      simp
    have hcone := coneBoundaryF ((n+1)+1) n
      (unif (Finset.univ : Finset (Fin (((n+1)+1)+1))) Finset.univ_nonempty)
      (Bdry (n+1)) (Bdry_mem_affineSpan (n+1))
    have hcone0 : (((Submission.Blueprint.singC).obj (tSplx ((n+1)+1))).d ((n+1)+1) (n+1))
          (coneChain ((n+1)+1)
            (unif (Finset.univ : Finset (Fin (((n+1)+1)+1))) Finset.univ_nonempty) (n+1)
            (Bdry (n+1)))
        = (-1 : ℤ) ^ ((n+1)+1) • Bdry (n+1) := by
      rw [hcone, hcycle]
      simp
    rw [step, hcone0, smul_smul]
    have hsign : (-1 : ℤ) ^ ((n+1)+1) * (-1 : ℤ) ^ ((n+1)+1) = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨((n+1)+1), by ring⟩
    rw [hsign, one_smul]

/-! ## The fundamental recursion for the homotopy chain -/

/-- `homW n` is the cycle which is coned in the recursion defining `homChain (n+1)`. -/
def homW (n : ℕ) : chN (n+1) (n+1) :=
  Sd (n+1) - eGen (n+1) - phiF n (n+1) (homChain n)

/-- `homW n` is a combination of affine simplices. -/
lemma homW_mem_affineSpan (n : ℕ) : homW n ∈ affineSpan (n+1) (n+1) :=
  Submodule.sub_mem _ (Submodule.sub_mem _ (Sd_mem_affineSpan (n+1))
    (eGen_mem_affineSpan (n+1))) (phiF_mem_affineSpan n (homChain_mem_affineSpan' n))

/-- The defining recursion of `homChain`, in terms of `homW`. -/
lemma homChain_apply (n : ℕ) :
    homChain (n+1) = (-1 : ℤ) ^ (n+2) • coneChain (n+1)
      (unif (Finset.univ : Finset (Fin (n+2))) Finset.univ_nonempty) (n+1) (homW n) := rfl

/-- The boundary of the fundamental identity simplex of `Δ^{n+1}`. -/
lemma eGen_d (n : ℕ) :
    (((Submission.Blueprint.singC).obj (tSplx (n+1))).d (n+1) n) (eGen (n+1)) =
      (phi n).f n (eGen n) := by
  rw [show eGen (n+1) = gen (tSplx (n+1)) (n+1) (ContinuousMap.id _) from rfl, gen_d,
    show eGen n = gen (tSplx n) n (ContinuousMap.id _) from rfl, phi_f_eq n n]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [gen_map]
  simp

/-- `phi` is compatible with the differential, elementwise, in every degree. -/
lemma phi_comm_apply'' (n k : ℕ) (s : chN n (k+1)) :
    (((Submission.Blueprint.singC).obj (tSplx (n+1))).d (k+1) k) ((phi n).f (k+1) s) =
      (phi n).f k ((((Submission.Blueprint.singC).obj (tSplx n)).d (k+1) k) s) :=
  congrArg (fun m => m s) (HomologicalComplex.Hom.comm (phi n) (k+1) k)

/-- The chain level step: coning the cycle `homW n` and taking the boundary returns `homW n`. -/
lemma homChain_rec_aux (n : ℕ)
    (hcyc : (((Submission.Blueprint.singC).obj (tSplx (n+1))).d (n+1) n) (homW n) = 0) :
    (((Submission.Blueprint.singC).obj (tSplx (n+1))).d (n+2) (n+1)) (homChain (n+1)) =
      homW n := by
  have hcone := coneBoundaryF (n+1) n
    (unif (Finset.univ : Finset (Fin (n+2))) Finset.univ_nonempty) (homW n)
    (homW_mem_affineSpan n)
  have step : (((Submission.Blueprint.singC).obj (tSplx (n+1))).d (n+2) (n+1))
        (homChain (n+1))
      = (-1 : ℤ) ^ (n+2) • (((Submission.Blueprint.singC).obj (tSplx (n+1))).d (n+2) (n+1))
          (coneChain (n+1) (unif (Finset.univ : Finset (Fin (n+2))) Finset.univ_nonempty)
            (n+1) (homW n)) := by
    rw [homChain_apply n]
    simp
  rw [step, hcone, hcyc, map_zero, add_zero, smul_smul]
  rw [show (-1 : ℤ) ^ (n+2) * (-1 : ℤ) ^ (n+2) = 1 from by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨n+2, by ring⟩, one_smul]

/-- **The fundamental recursion for the homotopy chain**:
`∂ (homChain (n+1)) = Sd (n+1) - eGen (n+1) - Φ (homChain n)`. -/
theorem homChain_rec (n : ℕ) :
    (((Submission.Blueprint.singC).obj (tSplx (n+1))).d (n+2) (n+1)) (homChain (n+1)) =
      homW n := by
  induction n with
  | zero =>
    refine homChain_rec_aux 0 ?_
    rw [show homW 0 = Sd (0+1) - eGen (0+1) - phiF 0 (0+1) (homChain 0) from rfl]
    simp only [phiF]
    rw [map_sub, map_sub, Sd_d_final 0, show Bdry 0 = (phi 0).f 0 (Sd 0) from rfl, eGen_d 0,
      phi_comm_apply'' 0 0 (homChain 0), show Sd 0 = eGen 0 from rfl,
      show homChain 0 = 0 from rfl]
    simp
  | succ n ih =>
    refine homChain_rec_aux (n+1) ?_
    have ih' : (((Submission.Blueprint.singC).obj (tSplx (n+1))).d ((n+1)+1) (n+1))
        (homChain (n+1)) = homW n := ih
    rw [show homW (n+1) = Sd ((n+1)+1) - eGen ((n+1)+1) -
        phiF (n+1) ((n+1)+1) (homChain (n+1)) from rfl]
    simp only [phiF]
    rw [map_sub, map_sub, Sd_d_final (n+1),
      show Bdry (n+1) = (phi (n+1)).f (n+1) (Sd (n+1)) from rfl, eGen_d (n+1),
      phi_comm_apply'' (n+1) (n+1) (homChain (n+1)), ih',
      show homW n = Sd (n+1) - eGen (n+1) - phiF n (n+1) (homChain n) from rfl]
    simp only [phiF]
    rw [map_sub, map_sub]
    have hzero : (phi (n+1)).f (n+1) ((phi n).f (n+1) (homChain n)) = 0 := by
      rw [← CategoryTheory.comp_apply, ← HomologicalComplex.comp_f, phi_comp_phi_sd n]
      simp
    rw [hzero]
    abel

/-! ## The homotopy identity -/

/-- The defining property of `homdeg` on the summand inclusions. -/
lemma homdeg_fac (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    genHom X n x ≫ homdeg X n
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (chX X (n+1))
          (((Submission.Blueprint.singC).map (TopCat.ofHom ((singEquiv X n) x))).f (n+1)
            (homChain n))) :=
  Cofan.IsColimit.fac ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n) _ x

/-- **The value of `homdeg` on a generator**: the pushforward of `homChain n`. -/
lemma homdeg_gen (X : TopCat) (n : ℕ) (σ : singMap X n) :
    homdeg X n (gen X n σ) =
      ((Submission.Blueprint.singC).map (TopCat.ofHom σ)).f (n+1) (homChain n) := by
  let x := (singEquiv X n).symm σ
  have hfac := homdeg_fac X n x
  have h := congrArg (fun f => f (1 : ℤ)) hfac
  rw [CategoryTheory.comp_apply] at h
  rw [ModuleCat.ofHom_apply, LinearMap.toSpanSingleton_apply_one] at h
  have hx : (ConcreteCategory.hom (genHom X n x)) (1 : ℤ) = gen X n σ := rfl
  rw [hx] at h
  have hx2 : (singEquiv X n) x = σ := by simp [x]
  rw [hx2] at h
  exact h

/-- Pushing a chain forward along `σ ∘ δᵢ` is pushing forward along `σ` after `δᵢ`
(in every degree). -/
lemma push_comp' (X : TopCat) (m : ℕ) (σ : singMap X (m+1)) (i : Fin (m+2)) (k : ℕ)
    (y : chN m k) :
    ((Submission.Blueprint.singC).map (TopCat.ofHom (σ.comp (coface m i).hom))).f k y
      = ((Submission.Blueprint.singC).map (TopCat.ofHom σ)).f k
          (((Submission.Blueprint.singC).map (coface m i)).f k y) := by
  rw [show (Submission.Blueprint.singC).map (TopCat.ofHom (σ.comp (coface m i).hom))
      = (Submission.Blueprint.singC).map (coface m i) ≫
          (Submission.Blueprint.singC).map (TopCat.ofHom σ) from by
    rw [TopCat.ofHom_comp, Functor.map_comp]
    rfl]
  rw [HomologicalComplex.comp_f, CategoryTheory.comp_apply]

/-- **The value of `homdeg` on the boundary of a generator**: `Φ` applied to `homChain n`,
pushed forward along `σ`. -/
lemma homdeg_d_gen (X : TopCat) (n : ℕ) (σ : singMap X (n+1)) :
    homdeg X n (((Submission.Blueprint.singC).obj X).d (n+1) n (gen X (n+1) σ))
      = ((Submission.Blueprint.singC).map (TopCat.ofHom σ)).f (n+1)
          (phiF n (n+1) (homChain n)) := by
  rw [gen_d, map_sum]
  rw [show phiF n (n+1) (homChain n) = (phi n).f (n+1) (homChain n) from rfl,
    phi_apply_sum n (n+1) (homChain n)]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  calc homdeg X n (((-1 : ℤ) ^ (i : ℕ)) • gen X n (σ.comp ((coface n i).hom)))
      = ((-1 : ℤ) ^ (i : ℕ)) • homdeg X n (gen X n (σ.comp ((coface n i).hom))) :=
        map_smul_int' (homdeg X n).hom _ _
    _ = ((-1 : ℤ) ^ (i : ℕ)) • ((Submission.Blueprint.singC).map (TopCat.ofHom σ)).f (n+1)
          (((Submission.Blueprint.singC).map (coface n i)).f (n+1) (homChain n)) := by
        rw [homdeg_gen]
        exact congrArg _ (push_comp' X n σ i (n+1) (homChain n))
    _ = ((Submission.Blueprint.singC).map (TopCat.ofHom σ)).f (n+1)
          (((-1 : ℤ) ^ (i : ℕ)) • ((Submission.Blueprint.singC).map (coface n i)).f (n+1)
            (homChain n)) :=
        (map_smul_int' (((Submission.Blueprint.singC).map (TopCat.ofHom σ)).f (n+1)).hom
          _ _).symm

/-- **The homotopy identity on generators**: `∂ H + H ∂ = Sd - id` on `gen X (n+1) σ`. -/
lemma homdeg_spec_gen (X : TopCat) (n : ℕ) (σ : singMap X (n+1)) :
    (((Submission.Blueprint.singC).obj X).d (n+2) (n+1))
        (homdeg X (n+1) (gen X (n+1) σ)) +
      homdeg X n ((((Submission.Blueprint.singC).obj X).d (n+1) n) (gen X (n+1) σ)) =
      sddeg X (n+1) (gen X (n+1) σ) - gen X (n+1) σ := by
  have h1 : (((Submission.Blueprint.singC).obj X).d (n+2) (n+1))
        (homdeg X (n+1) (gen X (n+1) σ))
      = ((Submission.Blueprint.singC).map (TopCat.ofHom σ)).f (n+1)
          (Sd (n+1) - eGen (n+1) - phiF n (n+1) (homChain n)) := by
    rw [homdeg_gen]
    rw [show (((Submission.Blueprint.singC).obj X).d (n+2) (n+1))
          (((Submission.Blueprint.singC).map (TopCat.ofHom σ)).f (n+2) (homChain (n+1)))
        = ((Submission.Blueprint.singC).map (TopCat.ofHom σ)).f (n+1)
            (((Submission.Blueprint.singC).obj (tSplx (n+1))).d (n+2) (n+1) (homChain (n+1)))
        from chainMap_d_apply (tSplx (n+1)) X (TopCat.ofHom σ) (n+1) (homChain (n+1))]
    rw [show (((Submission.Blueprint.singC).obj (tSplx (n+1))).d (n+2) (n+1))
          (homChain (n+1)) = homW n from homChain_rec n]
    rfl
  have h2 := homdeg_d_gen X n σ
  have h3 : sddeg X (n+1) (gen X (n+1) σ)
      = ((Submission.Blueprint.singC).map (TopCat.ofHom σ)).f (n+1) (Sd (n+1)) :=
    sddeg_gen X (n+1) σ
  have h4 : ((Submission.Blueprint.singC).map (TopCat.ofHom σ)).f (n+1) (eGen (n+1))
      = gen X (n+1) σ := by
    rw [show eGen (n+1) = gen (tSplx (n+1)) (n+1) (ContinuousMap.id _) from rfl]
    rw [gen_map (tSplx (n+1)) X (n+1) (TopCat.ofHom σ) (ContinuousMap.id _)]
    simp
  rw [h1, h2, h3]
  simp only [map_sub]
  rw [h4]
  abel

theorem homdeg_spec (X : TopCat) (n : ℕ) (z : ((Submission.Blueprint.singC).obj X).X (n+1)) :
    (((Submission.Blueprint.singC).obj X).d (n+2) (n+1)) (Work.SingMV.homdeg X (n+1) z) +
        Work.SingMV.homdeg X n ((((Submission.Blueprint.singC).obj X).d (n+1) n) z) =
      Work.SingMV.sddeg X (n+1) z - z := by
  -- the difference of the two sides, as a linear map, vanishes on the generators
  let F : chX X (n+1) →ₗ[ℤ] chX X (n+1) :=
    (((Submission.Blueprint.singC).obj X).d (n+2) (n+1)).hom.comp (homdeg X (n+1)).hom
      + (homdeg X n).hom.comp (((Submission.Blueprint.singC).obj X).d (n+1) n).hom
      - (sddeg X (n+1)).hom + LinearMap.id
  have hgen : ∀ σ : singMap X (n+1), F (gen X (n+1) σ) = 0 := by
    intro σ
    simp only [F, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply]
    rw [homdeg_spec_gen X n σ]
    abel
  have hzero : ModuleCat.ofHom F = 0 := by
    apply genHom_hom_ext
    intro x
    apply hom_int_ext
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, ModuleCat.ofHom_apply]
    have hx : (ConcreteCategory.hom (genHom X (n+1) x)) (1 : ℤ) =
        gen X (n+1) (singEquiv X (n+1) x) := rfl
    rw [hx, hgen]
    simp
  have hF : F = 0 := by
    have h := congrArg ModuleCat.Hom.hom hzero
    simpa using h
  have hz : F z = 0 := by
    rw [hF]
    simp
  have key : (((Submission.Blueprint.singC).obj X).d (n+2) (n+1)) (homdeg X (n+1) z) +
        homdeg X n ((((Submission.Blueprint.singC).obj X).d (n+1) n) z)
        - (sddeg X (n+1) z - z) = 0 := by
    have h := hz
    simp only [F, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply] at h
    convert h using 1
    abel
  exact sub_eq_zero.mp key

end Work.SingMV

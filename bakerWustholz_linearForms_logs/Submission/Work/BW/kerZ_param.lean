import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.rowLat_split

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex
open Module

/-! ## Auxiliary lemmas for `kerZ_param` -/

/-- The product `∏ i, f ^ (a i)` of integer powers of a nonzero element `f` is the power
`f ^ (∑ i, a i)`. -/
lemma prod_zpow_eq_zpow_sum {ι : Type*} [Fintype ι] {G : Type*} [CommGroupWithZero G]
    (f : G) (hf : f ≠ 0) (a : ι → ℤ) : ∏ i, f ^ (a i) = f ^ (∑ i, a i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add₀ hf]

/-- **First half of the parametrisation.**  If `M * C = 0` then every nonzero tuple `T` yields a
solution `y i = ∏ k, T k ^ (C i k)` of the system `∏ i, y i ^ (M j i) = 1`. -/
lemma prod_zpow_row_eq_one {N ρ q : ℕ} (M : Matrix (Fin ρ) (Fin N) ℤ)
    (C : Matrix (Fin N) (Fin q) ℤ) (h : M * C = 0)
    (T : Fin q → ℂ) (hT : ∀ k, T k ≠ 0) (j : Fin ρ) :
    ∏ i : Fin N, (∏ k : Fin q, T k ^ (C i k)) ^ (M j i) = 1 := by
  have hzero : ∀ k : Fin q, (∑ i : Fin N, C i k * M j i) = 0 := by
    intro k
    have h1 : (∑ i : Fin N, M j i * C i k) = 0 := by
      have h2 := congrFun (congrFun h j) k
      simpa [Matrix.mul_apply] using h2
    rw [← h1]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  calc ∏ i : Fin N, (∏ k : Fin q, T k ^ (C i k)) ^ (M j i)
      = ∏ i : Fin N, ∏ k : Fin q, (T k ^ (C i k)) ^ (M j i) :=
        Finset.prod_congr rfl (fun i _ =>
          (Finset.prod_zpow (fun k => T k ^ (C i k)) Finset.univ (M j i)).symm)
    _ = ∏ i : Fin N, ∏ k : Fin q, T k ^ (C i k * M j i) :=
        Finset.prod_congr rfl (fun i _ =>
          Finset.prod_congr rfl (fun k _ => by rw [← zpow_mul]))
    _ = ∏ k : Fin q, ∏ i : Fin N, T k ^ (C i k * M j i) := Finset.prod_comm
    _ = ∏ k : Fin q, T k ^ (∑ i : Fin N, C i k * M j i) :=
        Finset.prod_congr rfl (fun k _ =>
          prod_zpow_eq_zpow_sum (T k) (hT k) (fun i => C i k * M j i))
    _ = 1 := Finset.prod_eq_one (fun k _ => by rw [hzero k, zpow_zero])

/-- The `i i'` entry of the identity matrix over `ℂ` is the cast of the corresponding entry
of the identity matrix over `ℤ`. -/
lemma one_apply_cast {N : ℕ} (i i' : Fin N) :
    (1 : Matrix (Fin N) (Fin N) ℂ) i i' = ((1 : Matrix (Fin N) (Fin N) ℤ) i i' : ℂ) := by
  rw [Matrix.one_apply, Matrix.one_apply, Int.cast_ite]
  by_cases h : i = i' <;> simp [h]

/-- **Second half of the parametrisation.**  If `C * P + S * M = 1` then every nonzero `y` with
`∏ i, y i ^ (M j i) = 1` for all `j` is a monomial in `N - ρ` parameters. -/
lemma param_of_split {N ρ : ℕ} (M : Matrix (Fin ρ) (Fin N) ℤ)
    (C : Matrix (Fin N) (Fin (N - ρ)) ℤ) (S : Matrix (Fin N) (Fin ρ) ℤ)
    (P : Matrix (Fin (N - ρ)) (Fin N) ℤ) (hCP : C * P + S * M = 1) :
    ∀ y : Fin N → ℂ, (∀ i, y i ≠ 0) → (∀ j, ∏ i : Fin N, y i ^ (M j i) = 1) →
      ∃ T : Fin (N - ρ) → ℂ, (∀ k, T k ≠ 0) ∧
        ∀ i : Fin N, y i = ∏ k : Fin (N - ρ), T k ^ (C i k) := by
  classical
  intro y hy hy1
  -- principal logarithms
  set z : Fin N → ℂ := fun i => Complex.log (y i) with hzdef
  have hz : ∀ i, Complex.exp (z i) = y i := fun i => Complex.exp_log (hy i)
  -- integer "winding numbers" of `M z`
  have hw : ∀ j : Fin ρ, ∃ w : ℤ,
      (∑ i : Fin N, (M j i : ℂ) * z i) = (w : ℂ) * (2 * Real.pi * Complex.I) := by
    intro j
    refine Complex.exp_eq_one_iff.mp ?_
    calc Complex.exp (∑ i : Fin N, (M j i : ℂ) * z i)
        = ∏ i : Fin N, Complex.exp ((M j i : ℂ) * z i) := by
          simpa using Complex.exp_sum (Finset.univ : Finset (Fin N))
            (fun i => (M j i : ℂ) * z i)
      _ = ∏ i : Fin N, y i ^ (M j i) := by
          refine Finset.prod_congr rfl (fun i _ => ?_)
          rw [Complex.exp_int_mul, hz i]
      _ = 1 := hy1 j
  choose w hwval using hw
  -- the complexified matrices
  let Cc : Matrix (Fin N) (Fin (N - ρ)) ℂ := fun i k => (C i k : ℂ)
  let Pc : Matrix (Fin (N - ρ)) (Fin N) ℂ := fun k i => (P k i : ℂ)
  let Sc : Matrix (Fin N) (Fin ρ) ℂ := fun i j => (S i j : ℂ)
  let Mc : Matrix (Fin ρ) (Fin N) ℂ := fun j i => (M j i : ℂ)
  have hmat : Cc * Pc + Sc * Mc = (1 : Matrix (Fin N) (Fin N) ℂ) := by
    ext i i'
    have h1 := congrFun (congrFun hCP i) i'
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply] at h1
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Cc, Pc, Sc, Mc]
    rw [one_apply_cast, ← h1]
    push_cast
    ring
  -- the parameters
  refine ⟨fun k => Complex.exp (∑ i : Fin N, (P k i : ℂ) * z i),
    fun k => Complex.exp_ne_zero _, ?_⟩
  intro i
  set m : ℤ := ∑ j : Fin ρ, S i j * w j with hmdef
  have hdecomp : z i = (∑ k : Fin (N - ρ), (C i k : ℂ) * (∑ i' : Fin N, (P k i' : ℂ) * z i'))
      + ((m : ℂ) * (2 * Real.pi * Complex.I)) := by
    have hcomp : (Cc.mulVec (Pc.mulVec z)) i + (Sc.mulVec (Mc.mulVec z)) i = z i := by
      have h := congrFun (show (Cc * Pc + Sc * Mc).mulVec z = z from by
        rw [hmat, Matrix.one_mulVec]) i
      rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h
      simp only [Pi.add_apply] at h
      exact h
    have hA : (Cc.mulVec (Pc.mulVec z)) i
        = ∑ k : Fin (N - ρ), (C i k : ℂ) * (∑ i' : Fin N, (P k i' : ℂ) * z i') := by
      rw [Matrix.mulVec_apply_eq_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Matrix.mulVec_apply_eq_sum]
    have hB : (Sc.mulVec (Mc.mulVec z)) i = (m : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [Matrix.mulVec_apply_eq_sum]
      have h5 : ∀ j : Fin ρ, (Mc.mulVec z) j = (w j : ℂ) * (2 * Real.pi * Complex.I) := by
        intro j
        rw [Matrix.mulVec_apply_eq_sum]
        exact hwval j
      have hsum : (∑ j : Fin ρ, Sc i j * (Mc.mulVec z) j)
          = ∑ j : Fin ρ, Sc i j * ((w j : ℂ) * (2 * Real.pi * Complex.I)) :=
        Finset.sum_congr rfl (fun j _ => by rw [h5 j])
      rw [hsum]
      have h2 : (∑ j : Fin ρ, Sc i j * ((w j : ℂ) * (2 * Real.pi * Complex.I)))
          = (∑ j : Fin ρ, (S i j : ℂ) * (w j : ℂ)) * (2 * Real.pi * Complex.I) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [Sc]
        ring
      rw [h2]
      have hcast : (∑ j : Fin ρ, (S i j : ℂ) * (w j : ℂ))
          = ((∑ j : Fin ρ, S i j * w j : ℤ) : ℂ) := by
        push_cast
        rfl
      rw [hcast, ← hmdef]
    rw [← hcomp, hA, hB]
  -- conclusion
  calc y i = Complex.exp (z i) := (hz i).symm
    _ = Complex.exp ((∑ k : Fin (N - ρ), (C i k : ℂ) * (∑ i' : Fin N, (P k i' : ℂ) * z i'))
          + ((m : ℂ) * (2 * Real.pi * Complex.I))) := by rw [hdecomp]
    _ = Complex.exp (∑ k : Fin (N - ρ), (C i k : ℂ) * (∑ i' : Fin N, (P k i' : ℂ) * z i'))
          * Complex.exp ((m : ℂ) * (2 * Real.pi * Complex.I)) := Complex.exp_add _ _
    _ = Complex.exp (∑ k : Fin (N - ρ), (C i k : ℂ) * (∑ i' : Fin N, (P k i' : ℂ) * z i')) := by
          rw [show Complex.exp ((m : ℂ) * (2 * Real.pi * Complex.I)) = 1 from
            Complex.exp_eq_one_iff.mpr ⟨m, by ring⟩, mul_one]
    _ = ∏ k : Fin (N - ρ), Complex.exp ((C i k : ℂ) * (∑ i' : Fin N, (P k i' : ℂ) * z i')) := by
          simpa using Complex.exp_sum (Finset.univ : Finset (Fin (N - ρ)))
            (fun k => (C i k : ℂ) * (∑ i' : Fin N, (P k i' : ℂ) * z i'))
    _ = ∏ k : Fin (N - ρ), (Complex.exp (∑ i' : Fin N, (P k i' : ℂ) * z i')) ^ (C i k) := by
          refine Finset.prod_congr rfl (fun k _ => ?_)
          rw [Complex.exp_int_mul]

/-- **Splitting of the kernel lattice.** If `M * S = 1` then the kernel of `M` is a direct
summand with a `ℤ`-basis of `N - ρ` elements: there are matrices `C`, `P` with `M * C = 0` and
`C * P + S * M = 1`. -/
lemma ker_split_matrix_aux {N ρ : ℕ} (M : Matrix (Fin ρ) (Fin N) ℤ) (S : Matrix (Fin N) (Fin ρ) ℤ)
    (hρ : ρ ≤ N) (hS : M * S = 1) :
    ∃ (C : Matrix (Fin N) (Fin (N - ρ)) ℤ) (P : Matrix (Fin (N - ρ)) (Fin N) ℤ),
      M * C = 0 ∧ C * P + S * M = 1 := by
  classical
  set L : Submodule ℤ (Fin N → ℤ) := LinearMap.ker (Matrix.mulVecLin M) with hL
  have hLmem : ∀ x : Fin N → ℤ, x ∈ L ↔ M.mulVec x = 0 := by
    intro x
    rw [hL, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  let T : (Fin N → ℤ) →ₗ[ℤ] L := LinearMap.codRestrict L
    (LinearMap.id - (Matrix.mulVecLin S).comp (Matrix.mulVecLin M))
    (fun z => by
      rw [hLmem]
      show M.mulVec (z - S.mulVec (M.mulVec z)) = 0
      rw [Matrix.mulVec_sub, sub_eq_zero, Matrix.mulVec_mulVec, hS, Matrix.one_mulVec])
  have T_coe : ∀ z : Fin N → ℤ, ((T z : L) : Fin N → ℤ) = z - S.mulVec (M.mulVec z) := by
    intro z
    simp only [T, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply, Matrix.mulVecLin_apply]
  have hadd : ∀ (x y : L), ((x + y : L) : Fin N → ℤ) = (x : Fin N → ℤ) + (y : Fin N → ℤ) :=
    fun x y => map_add (Submodule.subtype L) x y
  have hsmul : ∀ (c : ℤ) (x : L), ((c • x : L) : Fin N → ℤ) = c • (x : Fin N → ℤ) :=
    fun c x => map_smul (Submodule.subtype L) c x
  have hinj : Function.Injective
      (fun p : L × (Fin ρ → ℤ) => (p.1 : Fin N → ℤ) + S.mulVec p.2) := by
    rintro ⟨a, u⟩ ⟨b, v⟩ h
    dsimp only at h
    have hpu : M.mulVec ((a : Fin N → ℤ) + S.mulVec u) = u := by
      rw [Matrix.mulVec_add, (hLmem a).mp a.2, zero_add, Matrix.mulVec_mulVec, hS,
        Matrix.one_mulVec]
    have hpv : M.mulVec ((b : Fin N → ℤ) + S.mulVec v) = v := by
      rw [Matrix.mulVec_add, (hLmem b).mp b.2, zero_add, Matrix.mulVec_mulVec, hS,
        Matrix.one_mulVec]
    have huv : u = v := by rw [← hpu, h, hpv]
    have hab : (a : Fin N → ℤ) = (b : Fin N → ℤ) := by
      rw [huv] at h
      exact add_right_cancel h
    exact Prod.ext (Subtype.ext hab) huv
  have hsurj : Function.Surjective
      (fun p : L × (Fin ρ → ℤ) => (p.1 : Fin N → ℤ) + S.mulVec p.2) := by
    intro z
    refine ⟨(T z, M.mulVec z), ?_⟩
    show ((T z : L) : Fin N → ℤ) + S.mulVec (M.mulVec z) = z
    rw [T_coe]
    exact sub_add_cancel _ _
  let F : (L × (Fin ρ → ℤ)) →ₗ[ℤ] (Fin N → ℤ) :=
    { toFun := fun p => (p.1 : Fin N → ℤ) + S.mulVec p.2
      map_add' := by
        rintro ⟨a, u⟩ ⟨b, v⟩
        show ((a + b : L) : Fin N → ℤ) + S.mulVec (u + v)
            = ((a : Fin N → ℤ) + S.mulVec u) + ((b : Fin N → ℤ) + S.mulVec v)
        rw [hadd, Matrix.mulVec_add]
        abel
      map_smul' := by
        rintro c ⟨a, u⟩
        show ((c • a : L) : Fin N → ℤ) + S.mulVec (c • u)
            = c • ((a : Fin N → ℤ) + S.mulVec u)
        rw [hsmul, Matrix.mulVec_smul, smul_add] }
  let E : (L × (Fin ρ → ℤ)) ≃ₗ[ℤ] (Fin N → ℤ) := LinearEquiv.ofBijective F ⟨hinj, hsurj⟩
  obtain ⟨n, bL⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin N)) L
  have hcard : n + ρ = N := by
    have bmap : Basis (Fin n ⊕ Fin ρ) ℤ (Fin N → ℤ) :=
      (bL.prod (Pi.basisFun ℤ (Fin ρ))).map E
    have h1 := Module.finrank_eq_card_basis bmap
    have h2 : Module.finrank ℤ (Fin N → ℤ) = N := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rw [h2, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h1
    exact h1.symm
  have hn : n = N - ρ := by omega
  let e' : Fin n ≃ Fin (N - ρ) := Fintype.equivOfCardEq (by simp [hn])
  let bL' : Basis (Fin (N - ρ)) ℤ L := bL.reindex e'
  let C : Matrix (Fin N) (Fin (N - ρ)) ℤ := fun i k => ((bL' k : L) : Fin N → ℤ) i
  let Pm : Matrix (Fin (N - ρ)) (Fin N) ℤ := fun k i => (bL'.repr (T (Pi.single i 1))) k
  refine ⟨C, Pm, ?_, ?_⟩
  · ext j k
    have h0 : M.mulVec ((bL' k : L) : Fin N → ℤ) = 0 := (hLmem _).mp (bL' k).2
    have h1 := congrFun h0 j
    rw [Matrix.mulVec_apply_eq_sum] at h1
    rw [Matrix.mul_apply, Matrix.zero_apply]
    exact h1
  · refine Matrix.ext_of_mulVec_single (fun j => ?_)
    rw [Matrix.one_mulVec, Matrix.add_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
    have hSM' : S.mulVec (M.mulVec (Pi.single j 1)) = (S * M).col j := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    have hCP : (C * Pm).col j = ((T (Pi.single j 1) : L) : Fin N → ℤ) := by
      funext i
      have hsr := Basis.sum_repr bL' (T (Pi.single j 1))
      have hcoe := congrArg (Submodule.subtype L) hsr
      simp only [map_sum, map_smul] at hcoe
      have h2 := congrFun hcoe i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
      rw [Matrix.col_apply, Matrix.mul_apply]
      refine Eq.trans ?_ h2
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp only [C, Pm]
      exact mul_comm _ _
    rw [hCP, T_coe, hSM']
    exact sub_add_cancel _ _

lemma kerZ_param {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M) :
    ∃ c : Fin N → Fin (N - ρ) → ℤ,
      (∀ T : Fin (N - ρ) → ℂ, (∀ j, T j ≠ 0) →
        ∀ j : Fin ρ, ∏ i : Fin N, (∏ k : Fin (N - ρ), T k ^ (c i k)) ^ (M j i) = 1) ∧
      (∀ y : Fin N → ℂ, (∀ i, y i ≠ 0) → (∀ j : Fin ρ, ∏ i : Fin N, y i ^ (M j i) = 1) →
        ∃ T : Fin (N - ρ) → ℂ, (∀ k, T k ≠ 0) ∧
          ∀ i : Fin N, y i = ∏ k : Fin (N - ρ), T k ^ (c i k)) := by
  classical
  by_cases hρ : ρ ≤ N
  · let M' : Matrix (Fin ρ) (Fin N) ℤ := M
    obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin N) (Fin ρ) ℤ, M' * S = 1 := rowLat_split M' hρ hM
    obtain ⟨C, P, hMC, hCP⟩ := ker_split_matrix_aux M' S hρ hS
    exact ⟨fun i k => C i k,
      fun T hT j => prod_zpow_row_eq_one M' C hMC T hT j,
      fun y hy hy1 => param_of_split M' C S P hCP y hy hy1⟩
  · exfalso
    have h1 : Fintype.card (Fin ρ) ≤ Module.finrank ℚ (Fin N → ℚ) :=
      LinearIndependent.fintype_card_le_finrank hM.1
    simp only [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at h1
    omega

end Work.BW

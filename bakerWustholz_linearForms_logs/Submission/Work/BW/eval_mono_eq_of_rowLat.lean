import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.subgroup_rayDegAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! Evaluation of the monomial `mono N d b` at a cone point `conePt N y` is the character
`∏ᵢ yᵢ^{bᵢ}`; this is restated here so that the main lemma is self-contained (the sibling file
`Submission.Work.BW.eval_conePt_mono` is not imported). -/
lemma eval_conePt_mono_aux (N : ℕ) (d : Fin (N + 1) →₀ ℕ) (b : Fin (N + 1) → ℕ)
    (y : Fin (N + 1) → ℂ) :
    MvPolynomial.eval (conePt N y) (mono N d b) = ∏ i, y i ^ (b i) := by
  simp only [mono, map_prod]
  simp [conePt]

/-! ### The character `v ↦ ∏ᵢ zᵢ^{vᵢ}` is additive in the exponent -/

lemma prod_zpow_add_aux {N : ℕ} (z : Fin N → ℂ) (hz : ∀ i, z i ≠ 0) (a b : Fin N → ℤ) :
    ∏ i, z i ^ ((a + b) i) = (∏ i, z i ^ (a i)) * (∏ i, z i ^ (b i)) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [Pi.add_apply, zpow_add₀ (hz i)]

lemma prod_zpow_zsmul_aux {N : ℕ} (z : Fin N → ℂ) (c : ℤ) (a : Fin N → ℤ) :
    ∏ i, z i ^ ((c • a) i) = (∏ i, z i ^ (a i)) ^ c := by
  rw [← Finset.prod_zpow]
  apply Finset.prod_congr rfl
  intro i _
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, zpow_mul]

/-- Distributing the character over a finite integer combination of rows. -/
lemma prod_zpow_sum_aux {N ρ : ℕ} (z : Fin N → ℂ) (hz : ∀ i, z i ≠ 0)
    (c : Fin ρ → ℤ) (M : Fin ρ → Fin N → ℤ) (s : Finset (Fin ρ)) :
    ∏ i, z i ^ ((∑ j ∈ s, c j • M j) i) = ∏ j ∈ s, (∏ i, z i ^ (M j i)) ^ (c j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, prod_zpow_add_aux z hz,
          prod_zpow_zsmul_aux z (c a) (M a), ih]

/-- The character `v ↦ ∏ᵢ zᵢ^{vᵢ}` is trivial on the row lattice `rowLat M` whenever it is
trivial on each row `M j` (and the `zᵢ` are nonzero). -/
lemma prod_zpow_eq_one_of_mem_rowLat_aux {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (z : Fin N → ℂ)
    (hz : ∀ i, z i ≠ 0) (hker : ∀ j, ∏ i, z i ^ (M j i) = 1)
    {v : Fin N → ℤ} (hv : v ∈ rowLat N ρ M) :
    ∏ i, z i ^ (v i) = 1 := by
  rw [rowLat] at hv
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℤ)).mp hv
  rw [← hc, prod_zpow_sum_aux z hz c M Finset.univ]
  simp [hker]

/-- Two monomials of multidegree `d` whose exponent vectors have the same `X_{0,1}`-exponent and whose torus parts differ by an element of the row lattice `rowLat M` define the same function on `ker M`: if `b 0 = b' 0` and `(bᵢ)_{i≥1} - (b'ᵢ)_{i≥1} ∈ rowLat M`, then for every torus point `y` of `ker M` (`yᵢ ≠ 0`, `∏ᵢ yᵢ^{M_{ji}} = 1`), `∏ᵢ yᵢ^{bᵢ} = ∏ᵢ yᵢ^{b'ᵢ}`. (Use `eval_conePt_mono`, which may be proved inline if the file `Submission.Work.BW.eval_conePt_mono` is not available.) -/
theorem eval_mono_eq_of_rowLat {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (d : Fin (N + 1) →₀ ℕ)
    (b b' : Fin (N + 1) → ℕ) (h0 : b 0 = b' 0)
    (hcl : (fun i : Fin N => (b i.succ : ℤ)) - (fun i : Fin N => (b' i.succ : ℤ)) ∈ rowLat N ρ M)
    (y : Fin (N + 1) → ℂ) (hy : ∀ i : Fin N, y i.succ ≠ 0)
    (hker : ∀ j, ∏ i : Fin N, (y i.succ) ^ (M j i) = 1) :
    MvPolynomial.eval (conePt N y) (mono N d b) = MvPolynomial.eval (conePt N y) (mono N d b') := by
  -- the `X_{0,1}`-exponent is `b 0 = b' 0`, so it suffices to compare the torus parts
  have h1 : ∏ i : Fin N, (fun i => y i.succ) i ^ ((b i.succ : ℤ) - (b' i.succ : ℤ)) = 1 := by
    simpa [Pi.sub_apply] using
      prod_zpow_eq_one_of_mem_rowLat_aux M (fun i => y i.succ) (fun i => hy i)
        (fun j => hker j) hcl
  have hbody : ∏ i : Fin N, y i.succ ^ b i.succ = ∏ i : Fin N, y i.succ ^ b' i.succ := by
    have h2 : ∏ i : Fin N, (fun i => y i.succ) i ^ (b i.succ : ℤ) =
        ∏ i : Fin N, (fun i => y i.succ) i ^ (b' i.succ : ℤ) := by
      calc ∏ i : Fin N, (fun i => y i.succ) i ^ (b i.succ : ℤ)
          = ∏ i : Fin N, (fun i => y i.succ) i ^
              ((b' i.succ : ℤ) + ((b i.succ : ℤ) - (b' i.succ : ℤ))) := by
            apply Finset.prod_congr rfl; intro i _; congr 1; ring
        _ = ∏ i : Fin N, (fun i => y i.succ) i ^ (b' i.succ : ℤ) *
              (fun i => y i.succ) i ^ ((b i.succ : ℤ) - (b' i.succ : ℤ)) := by
            apply Finset.prod_congr rfl; intro i _; rw [zpow_add₀ (hy i)]
        _ = (∏ i : Fin N, (fun i => y i.succ) i ^ (b' i.succ : ℤ)) *
              (∏ i : Fin N, (fun i => y i.succ) i ^ ((b i.succ : ℤ) - (b' i.succ : ℤ))) := by
            rw [Finset.prod_mul_distrib]
        _ = (∏ i : Fin N, (fun i => y i.succ) i ^ (b' i.succ : ℤ)) * 1 := by rw [h1]
        _ = ∏ i : Fin N, (fun i => y i.succ) i ^ (b' i.succ : ℤ) := by rw [mul_one]
    simpa using h2
  rw [eval_conePt_mono_aux, eval_conePt_mono_aux, Fin.prod_univ_succ, Fin.prod_univ_succ, h0, hbody]

end Work.BW

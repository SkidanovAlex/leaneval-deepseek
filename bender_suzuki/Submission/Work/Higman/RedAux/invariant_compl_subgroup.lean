import Mathlib
import Submission.Work.Higman.RedAux.crux_helpers
import Submission.Work.Higman.RedAux.elem_abelian_invariant_compl
import Submission.Work.Higman.RedAux.map_comap_mulEquiv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace Work.Higman.RedAux

/-- **Invariant complement of `C` modulo `A`.**

Let `A ⊴ P` be normal with `A ≤ C ≤ P`, suppose `P/A` is an elementary abelian `2`-group
(`⁅x,y⁆ ∈ A` and `x² ∈ A` for all `x, y`), and let `ξ` be an automorphism of `P` fixing both `A`
and `C`, whose `e`-th power acts trivially on `P/A` with `e` odd.  Then there is a `ξ`-invariant
subgroup `N` with `A ≤ N`, `N ⊓ C = A` and `N ⊔ C = ⊤`.

The proof works in the quotient `Q = P/A`, an `𝔽₂`-vector space on which `ξ` induces an
automorphism `σ` of odd order.  The subgroup `S = C/A` is `σ`-invariant, so Maschke for an
odd-order operator on an elementary abelian `2`-group
(`RedAux.elem_abelian_invariant_compl`, itself derived from `RedAux.odd_compl`) provides a
`σ`-invariant complement `N̄` of `S`; pulling `N̄` back to `P` gives `N`. -/
theorem invariant_compl_subgroup {P : Type} [Group P] [Finite P]
    (ξ : MulAut P) {A C : Subgroup P} (hAn : A.Normal)
    (hAinv : A.map (ξ : MulAut P).toMonoidHom = A) (hAC : A ≤ C)
    (hCinv : C.map (ξ : MulAut P).toMonoidHom = C)
    (hAb : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ A) (h2 : ∀ x : P, x ^ 2 ∈ A)
    {e : ℕ} (he : Odd e) (he1 : ∀ x : P, (ξ ^ e) x * x⁻¹ ∈ A) :
    ∃ N : Subgroup P, A ≤ N ∧ N.map (ξ : MulAut P).toMonoidHom = N ∧ N ⊓ C = A ∧ N ⊔ C = ⊤ := by
  classical
  letI := hAn
  -- `Q := P ⧸ A` is commutative, because every commutator lies in `A`.
  have hcomm : ∀ a b : P ⧸ A, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective A a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective A b
    have hxy : x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    have hker : (QuotientGroup.mk' A) (x * y * x⁻¹ * y⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact hAb x y
    rw [← map_mul, ← map_mul, hxy, map_mul, hker, one_mul]
  let π : P →* P ⧸ A := QuotientGroup.mk' A
  have hkerπ : π.ker = A := QuotientGroup.ker_mk' A
  -- every element of `Q` has order dividing `2`, because every square lies in `A`.
  have h2Q : ∀ q : P ⧸ A, q ^ 2 = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective A q
    have hk : (QuotientGroup.mk' A) (x ^ 2) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact h2 x
    rw [← map_pow, hk]
  -- the automorphism induced by `ξ` on `Q`
  let σ : MulAut (P ⧸ A) := QuotientGroup.congr A A ξ hAinv
  have hc : ∀ x : P, σ (π x) = π (ξ x) := fun x => QuotientGroup.congr_mk' A A ξ hAinv x
  have hpow : ∀ k : ℕ, ∀ x : P, (σ ^ k) (π x) = π ((ξ ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', MulAut.coe_mul, Function.comp_apply, ih, hc, pow_succ', MulAut.coe_mul,
        Function.comp_apply]
  have hfin : ∀ x : P, (σ ^ e) (π x) = π x := by
    intro x
    rw [hpow e x]
    have hg : (ξ ^ e) x * x⁻¹ ∈ A := he1 x
    have hk : π ((ξ ^ e) x * x⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, hkerπ]; exact hg
    calc π ((ξ ^ e) x) = π (((ξ ^ e) x * x⁻¹) * x) := by
          rw [show ((ξ ^ e) x * x⁻¹) * x = (ξ ^ e) x by group]
      _ = π ((ξ ^ e) x * x⁻¹) * π x := map_mul π _ _
      _ = 1 * π x := by rw [hk]
      _ = π x := one_mul _
  have hσ : σ ^ e = 1 := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective A q
    exact hfin x
  -- `S = C/A`, invariant under `σ`
  let S : Subgroup (P ⧸ A) := Subgroup.map π C
  have hS : ∀ x ∈ S, σ x ∈ S := by
    intro x hx
    obtain ⟨c, hcC, rfl⟩ := Subgroup.mem_map.mp hx
    have hξc : ξ c ∈ C := by
      have hmem : ξ c ∈ C.map (ξ : MulAut P).toMonoidHom := Subgroup.mem_map.mpr ⟨c, hcC, rfl⟩
      rwa [hCinv] at hmem
    rw [hc c]
    exact Subgroup.mem_map.mpr ⟨ξ c, hξc, rfl⟩
  -- Maschke: a `σ`-invariant complement `N̄` of `S` in `Q`.
  -- (The `CommGroup` instance on `Q` is deliberately local: it must not be in scope for the
  -- quotient computations above, where it would change the `One` instance of `P ⧸ A`.)
  have key : ∃ Nq : Subgroup (P ⧸ A), (∀ x ∈ Nq, σ x ∈ Nq) ∧ S ⊓ Nq = ⊥ ∧ S ⊔ Nq = ⊤ := by
    letI : CommGroup (P ⧸ A) := { (inferInstance : Group (P ⧸ A)) with mul_comm := hcomm }
    exact elem_abelian_invariant_compl h2Q σ he hσ S hS
  obtain ⟨Nq, hNqinv, hNqinf, hNqsup⟩ := key
  -- upgrade the one-sided invariance to `Nq.map σ = Nq`
  have hmapNq : Nq.map (σ : (P ⧸ A) →* (P ⧸ A)) = Nq := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact hNqinv x hx
    · intro y hy
      have hiter : ∀ k : ℕ, (σ ^ k) y ∈ Nq := by
        intro k
        induction k with
        | zero => simpa using hy
        | succ k ih =>
          rw [pow_succ', MulAut.coe_mul, Function.comp_apply]
          exact hNqinv _ ih
      have hy1 : (σ ^ (e - 1)) y ∈ Nq := hiter (e - 1)
      refine Subgroup.mem_map.mpr ⟨(σ ^ (e - 1)) y, hy1, ?_⟩
      have hee : σ * σ ^ (e - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel he.pos]; exact hσ
      have hstep : σ ((σ ^ (e - 1)) y) = y := by
        have := congrArg (fun f : MulAut (P ⧸ A) => f y) hee
        simpa [MulAut.coe_mul, MulAut.coe_one, Function.comp_apply] using this
      exact hstep
  -- pull back to `N ≤ P`
  let N : Subgroup P := Subgroup.comap π Nq
  have hAN : A ≤ N := by
    intro a ha
    rw [Subgroup.mem_comap]
    have : π a = 1 := by rw [← MonoidHom.mem_ker, hkerπ]; exact ha
    rw [this]; exact Nq.one_mem
  have hmapN : Subgroup.map π N = Nq := by
    change Subgroup.map π (Subgroup.comap π Nq) = Nq
    exact Subgroup.map_comap_eq_self (f := π) (H := Nq)
      (by rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective A)]; exact le_top)
  have hcomapbot : (⊥ : Subgroup (P ⧸ A)).comap π = A := hkerπ
  refine ⟨N, hAN, ?_, ?_, ?_⟩
  · -- `ξ`-invariance of `N`
    have h := map_comap_mulEquiv π ξ σ hc Nq
    rw [hmapNq] at h
    change Subgroup.map (ξ : MulAut P).toMonoidHom (Subgroup.comap π Nq) = Subgroup.comap π Nq
    exact h
  · -- `N ⊓ C = A`
    apply le_antisymm
    · have hle : Subgroup.map π (N ⊓ C) ≤ (⊥ : Subgroup (P ⧸ A)) := by
        calc Subgroup.map π (N ⊓ C) ≤ Subgroup.map π N ⊓ Subgroup.map π C :=
              Subgroup.map_inf_le N C π
          _ = Nq ⊓ S := by rw [hmapN]
          _ = ⊥ := by rw [inf_comm]; exact hNqinf
      rw [Subgroup.map_le_iff_le_comap, hcomapbot] at hle
      exact hle
    · exact le_inf hAN hAC
  · -- `N ⊔ C = ⊤`
    have hmapNC : Subgroup.map π (N ⊔ C) = ⊤ := by
      rw [Subgroup.map_sup, hmapN]
      change Nq ⊔ S = ⊤
      rw [sup_comm]; exact hNqsup
    have h1 : (N ⊔ C) ⊔ A = ⊤ := by
      have hcm := Subgroup.comap_map_eq π (N ⊔ C)
      rw [hmapNC, Subgroup.comap_top, hkerπ] at hcm
      exact hcm.symm
    rw [← h1, sup_eq_left.mpr (hAN.trans le_sup_left)]

end Work.Higman.RedAux

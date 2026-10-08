import Mathlib
import Submission.Work.BrauerSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Quaternion

/-!
# Normal form in a generalized quaternion group

Let `P = ⟨τ, ρ⟩` be a generalized quaternion group in Dade's normal form
(`Work.BrauerSuzuki.GenQuaternionData`), i.e. `τ` has order `2 ^ n` (`n ≥ 2`),
`ρ τ ρ⁻¹ = τ⁻¹` and `ρ ^ 2 = τ ^ (2 ^ (n-1))`.  Then every element of `P` is a power of `τ`
or of the shape `ρ * τ ^ i`; the two families have `2 ^ n` elements each and exhaust the group
of order `2 ^ (n+1)`.

Here we prove exactly the statement announced: every `g : P` lies in
`Subgroup.zpowers τ ∪ ρ · (Subgroup.zpowers τ)`.  The proof follows the outline of the
statement's docstring:

* `τ ^ i = (ρ⁻¹ τ ρ)^i` style conjugation: the subgroup `⟨τ⟩` is invariant under conjugation
  by `ρ⁻¹` (because `ρ⁻¹ τ ρ = τ⁻¹`), which lets one push a factor `ρ` past a power of `τ`;
* since `τ` has finite order, every element of `Subgroup.zpowers τ` is a *natural* power
  `τ ^ i` (needed because the second family is indexed by `ℕ`);
* the set `A = ⟨τ⟩ ∪ ρ⟨τ⟩` is closed under multiplication and inversion and contains `τ`
  and `ρ`, hence contains `Subgroup.closure {τ, ρ} = ⊤`.
-/

variable {P : Type*} [Group P]

/-- The "normal form" predicate: `x` is a power of `tau`, or `rho` times a power of `tau`. -/
private def NF (d : GenQuaternionData P) (x : P) : Prop :=
  x ∈ Subgroup.zpowers d.tau ∨ ∃ i : ℕ, x = d.rho * d.tau ^ i

/-- Conjugation by `rho⁻¹` inverts `tau` as well: `ρ⁻¹ τ ρ = τ⁻¹`. -/
private lemma conj_rho_inv_tau (d : GenQuaternionData P) :
    d.rho⁻¹ * d.tau * d.rho = d.tau⁻¹ := by
  have h1 : d.tau * d.rho⁻¹ = d.rho⁻¹ * d.tau⁻¹ := by
    rw [← d.rho_conj]; group
  have h2 : d.tau = d.rho⁻¹ * d.tau⁻¹ * d.rho := by
    rw [← h1]; group
  calc d.rho⁻¹ * d.tau * d.rho = (d.rho⁻¹ * d.tau⁻¹ * d.rho)⁻¹ := by group
    _ = d.tau⁻¹ := by rw [← h2]

/-- Because `tau` has finite order, every element of `Subgroup.zpowers tau` is a natural
power of `tau`. -/
private lemma zpowers_tau_eq_pow (d : GenQuaternionData P) {z : P}
    (hz : z ∈ Subgroup.zpowers d.tau) : ∃ i : ℕ, z = d.tau ^ i := by
  have hfin : IsOfFinOrder d.tau := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨2 ^ d.n, by positivity, by rw [← d.tau_order]; exact pow_orderOf_eq_one d.tau⟩
  have hz' : z ∈ Submonoid.powers d.tau := (hfin.mem_powers_iff_mem_zpowers).mpr hz
  obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff z d.tau).mp hz'
  exact ⟨i, hi.symm⟩

/-- `Subgroup.zpowers d.tau` is invariant under conjugation by `d.rho⁻¹`
(the conjugation homomorphism sends the generator `tau` to `tau⁻¹`). -/
private lemma conj_rho_inv_mem_zpowers (d : GenQuaternionData P) {z : P}
    (hz : z ∈ Subgroup.zpowers d.tau) : d.rho⁻¹ * z * d.rho ∈ Subgroup.zpowers d.tau := by
  have hle : Subgroup.zpowers d.tau ≤
      Subgroup.comap (MulAut.conj d.rho⁻¹).toMonoidHom (Subgroup.zpowers d.tau) := by
    rw [Subgroup.zpowers_le]
    simp [conj_rho_inv_tau d]
  simpa [MulAut.conj_apply] using hle hz

/-- `rho * rho = tau ^ (2 ^ (n-1))`. -/
private lemma rho_mul_rho (d : GenQuaternionData P) :
    d.rho * d.rho = d.tau ^ (2 ^ (d.n - 1)) := by
  rw [← pow_two, d.rho_sq]

/-- The set `A = ⟨τ⟩ ∪ ρ⟨τ⟩` is closed under multiplication. -/
private lemma NF_mul (d : GenQuaternionData P) {x y : P} (hx : NF d x) (hy : NF d y) :
    NF d (x * y) := by
  rcases hx with hx | ⟨i, rfl⟩
  · rcases hy with hy | ⟨j, rfl⟩
    · exact Or.inl (Subgroup.mul_mem _ hx hy)
    · -- `x ∈ ⟨τ⟩`, `y = ρ τ ^ j`
      obtain ⟨k, hk⟩ := zpowers_tau_eq_pow d (conj_rho_inv_mem_zpowers d hx)
      refine Or.inr ⟨k + j, ?_⟩
      rw [pow_add, ← hk]
      group
  · rcases hy with hy | ⟨j, rfl⟩
    · -- `x = ρ τ ^ i`, `y ∈ ⟨τ⟩`
      obtain ⟨k, hk⟩ := zpowers_tau_eq_pow d
        (Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers d.tau i) hy)
      refine Or.inr ⟨k, ?_⟩
      rw [← hk]
      group
    · -- `x = ρ τ ^ i`, `y = ρ τ ^ j`
      have key : (d.rho * d.tau ^ i) * (d.rho * d.tau ^ j)
          = d.tau ^ (2 ^ (d.n - 1)) * ((d.rho⁻¹ * d.tau ^ i * d.rho) * d.tau ^ j) := by
        rw [← rho_mul_rho d]; group
      obtain ⟨k, hk⟩ := zpowers_tau_eq_pow d (Subgroup.mul_mem _
        (conj_rho_inv_mem_zpowers d (Subgroup.npow_mem_zpowers d.tau i))
        (Subgroup.npow_mem_zpowers d.tau j))
      refine Or.inl ?_
      rw [key, hk]
      exact Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers d.tau (2 ^ (d.n - 1)))
        (Subgroup.npow_mem_zpowers d.tau k)

/-- The set `A = ⟨τ⟩ ∪ ρ⟨τ⟩` is closed under inversion. -/
private lemma NF_inv (d : GenQuaternionData P) {x : P} (hx : NF d x) : NF d x⁻¹ := by
  rcases hx with hx | ⟨i, rfl⟩
  · exact Or.inl (Subgroup.inv_mem _ hx)
  · -- `x = ρ τ ^ i`, so `x⁻¹ = τ^{-i} ρ⁻¹ = ρ (ρ⁻¹ τ^{-i} ρ) (τ ^ (2^(n-1)))⁻¹`
    obtain ⟨k, hk⟩ := zpowers_tau_eq_pow d (Subgroup.mul_mem _
      (conj_rho_inv_mem_zpowers d (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers d.tau i)))
      (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers d.tau (2 ^ (d.n - 1)))))
    refine Or.inr ⟨k, ?_⟩
    have key : (d.rho * d.tau ^ i)⁻¹
        = d.rho * ((d.rho⁻¹ * (d.tau ^ i)⁻¹ * d.rho) * (d.tau ^ (2 ^ (d.n - 1)))⁻¹) := by
      rw [← rho_mul_rho d]; group
    rw [key, hk]

/-- Normal form for a generalized quaternion group given by `GenQuaternionData d`:
every element is either a power of `tau` or of the form `rho * tau ^ i`.  Proof: the set
`Subgroup.zpowers d.tau ∪ d.rho • Subgroup.zpowers d.tau` is closed under multiplication
(using `rho_conj`, `rho_sq`) and contains `tau` and `rho`, so it is a subgroup containing the
generating set; hence it is everything. -/
theorem genQuaternionData_mem_or (P : Type*) [Group P] (d : Work.BrauerSuzuki.GenQuaternionData P)
    (g : P) : g ∈ Subgroup.zpowers d.tau ∨ ∃ i : ℕ, g = d.rho * d.tau ^ i := by
  change NF d g
  have hone : NF d 1 := Or.inl (Subgroup.one_mem _)
  have hgen : ∀ x ∈ ({d.tau, d.rho} : Set P), NF d x := by
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact Or.inl (Subgroup.mem_zpowers d.tau)
    · rw [hx]; exact Or.inr ⟨0, by simp⟩
  exact Subgroup.closure_induction (p := fun x _ => NF d x) hgen hone
    (fun x y _ _ => NF_mul d) (fun x _ => NF_inv d)
    (x := g) (by rw [d.closure_eq_top]; exact Subgroup.mem_top g)

end Work.BrauerSuzuki.Quaternion

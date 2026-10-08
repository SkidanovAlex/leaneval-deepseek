import Mathlib
import Submission.Work.CharPrelim.Defs
import Submission.Work.CharPrelim.exists_extension_rep
import Submission.Work.CharPrelim.exists_normalized_intertwiner

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharPrelim.extend_char_of_cyclic_quotient`

**Character extension across a cyclic quotient.**  If `K ⊴ G` with `G ⧸ K` cyclic and
`ψ ∈ Irr K` is `G`-invariant, then `ψ` extends to an irreducible character of `G`.

The proof is the classical cocycle-free construction.  Fix `g₀ : G` whose image generates
`G ⧸ K` and let `n` be its order in the quotient.  Given an irreducible representation
`ρ` of `↥K` realising `ψ`, invariance produces a linear equivalence `P₀` intertwining `ρ`
with its `g₀`-conjugate.  Multiplying `P₀` by a suitable scalar `μ` (Schur's lemma — the
discrepancy `ρ(g₀ⁿ)⁻¹P₀ⁿ` is a scalar) makes it satisfy `P ^ n = ρ (g₀ ^ n)`.  Then
`R x := P^{i(x)} ρ(a(x))`, where `x = g₀^{i(x)} a(x)` with `a(x) ∈ K` and `0 ≤ i(x) < n`,
is a well defined homomorphism `G →* (V →ₗ[ℂ] V)` restricting to `ρ` on `K`; it is
irreducible because a `G`-invariant subspace is `K`-invariant.  Its character is the
required extension of `ψ`.
-/

noncomputable section

open Classical

namespace Work.CharPrelim

set_option linter.unusedSectionVars false

/-! ### Conjugation of a normal subgroup -/

/-- Conjugation by `g` as a multiplicative equivalence of a normal subgroup `K ≤ G`. -/
def conjAut {G : Type*} [Group G] (K : Subgroup G) [K.Normal] (g : G) : ↥K ≃* ↥K where
  toFun k := ⟨g * (k : G) * g⁻¹, (inferInstance : K.Normal).conj_mem (k : G) k.2 g⟩
  invFun k := ⟨g⁻¹ * (k : G) * g,
    by simpa using (inferInstance : K.Normal).conj_mem (k : G) k.2 g⁻¹⟩
  left_inv k := by ext; group
  right_inv k := by ext; group
  map_mul' a b := by ext; simp only [Subgroup.coe_mul, Subgroup.coe_mk]; group

@[simp]
theorem conjAut_coe {G : Type*} [Group G] {K : Subgroup G} [K.Normal] (g : G) (k : ↥K) :
    ((conjAut K g k : ↥K) : G) = g * (k : G) * g⁻¹ := rfl

theorem conjFun_eq_apply_conjAut {G : Type*} [Group G] {K : Subgroup G} [K.Normal] (g : G)
    (ψ : ↥K → ℂ) (k : ↥K) :
    Work.Clifford.conjFun K g ψ k = ψ (conjAut K g k) := by
  rw [Work.Clifford.conjFun_apply]
  congr 1

/-- The character of the `g`-conjugate representation is the `g`-conjugate function. -/
theorem character_comp_conjAut {G : Type*} [Group G] {K : Subgroup G} [K.Normal] (g : G)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ ↥K V) :
    Representation.character (ρ.comp (conjAut K g).toMonoidHom)
      = fun k => ρ.character (conjAut K g k) := rfl

/-! ### An irreducible representation is determined by its character -/

/-- Two finite dimensional complex representations of a finite group, one of them
irreducible, with the same character, are equivalent.

Indeed the multiplicity of `ρ` in `σ` is
`|G|⁻¹ ∑_g σ.character g * ρ.character g⁻¹`, which equals `1` because the characters agree
and `ρ` is irreducible; so there is a nonzero intertwining map `ρ → σ`, which is injective
by irreducibility of `ρ` and hence bijective because the two sides have the same dimension. -/
theorem nonempty_equiv_of_char_eq {G : Type*} [Group G] [Fintype G]
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (hρ : ρ.IsIrreducible) (h : ρ.character = σ.character) :
    Nonempty (ρ.Equiv σ) := by
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    have hc : 0 < Nat.card G := Nat.card_pos
    exact_mod_cast hc.ne')
  haveI : ρ.IsIrreducible := hρ
  have hsum : (Nat.card G : ℂ)⁻¹ * ∑ g, σ.character g * ρ.character g⁻¹ = 1 := by
    have h2 : (Nat.card G : ℂ)⁻¹ * ∑ g, σ.character g * ρ.character g⁻¹
        = (Nat.card G : ℂ)⁻¹ * ∑ g, ρ.character g * ρ.character g⁻¹ := by
      rw [← h]
    rw [h2, Representation.char_orthonormal ρ ρ, ite_eq_left ⟨Representation.Equiv.refl ρ⟩]
  have hfinC : ((Module.finrank ℂ (ρ.IntertwiningMap σ) : ℕ) : ℂ) = 1 := by
    rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ, hsum]
  have hfin : Module.finrank ℂ (ρ.IntertwiningMap σ) = 1 := by exact_mod_cast hfinC
  haveI : Nontrivial (ρ.IntertwiningMap σ) :=
    Module.nontrivial_of_finrank_pos (by rw [hfin]; norm_num)
  obtain ⟨f, hfne⟩ := exists_ne (0 : ρ.IntertwiningMap σ)
  have hinj : Function.Injective (⇑f) :=
    (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hfne
  have hdimC : ((Module.finrank ℂ V : ℕ) : ℂ) = (Module.finrank ℂ W : ℕ) := by
    rw [← Representation.char_one ρ, ← Representation.char_one σ, h]
  have hdim : Module.finrank ℂ V = Module.finrank ℂ W := by exact_mod_cast hdimC
  exact ⟨f.ofBijective
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩⟩

/-! ### The main theorem -/

theorem extend_char_of_cyclic_quotient {G : Type*} [Group G] [Fintype G] {K : Subgroup G}
    [K.Normal] [Fintype ↥K] {ψ : ↥K → ℂ} (hψ : ψ ∈ Work.CharCore.Irr ↥K)
    (hinv : Work.Clifford.inertia K ψ = ⊤) (hcyc : IsCyclic (G ⧸ K)) :
    ∃ χ : G → ℂ, χ ∈ Work.CharCore.Irr G ∧ Work.Clifford.Extends K χ ψ := by
  -- `ψ` is the character of an irreducible finite dimensional representation of `↥K`
  obtain ⟨W, hWsimple, hWchar⟩ := (Work.CharCore.mem_Irr_iff_fdrep ψ).mp hψ
  haveI : CategoryTheory.Simple W := hWsimple
  let ρ : Representation ℂ ↥K ↥W := W.ρ
  have hρirr : Representation.IsIrreducible ρ := (Work.CharCore.fdRep_simple_iff W).mp hWsimple
  have hρchar : Representation.character ρ = ψ := hWchar
  -- a generator of the cyclic quotient
  obtain ⟨gbar, hgbar⟩ := hcyc.exists_generator
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective (s := K) gbar
  have hgen : ∀ x : G, ∃ i : ℤ, (QuotientGroup.mk' K g₀) ^ i = (QuotientGroup.mk' K) x := by
    intro x
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgbar (QuotientGroup.mk x))
    refine ⟨i, ?_⟩
    have h2 : (QuotientGroup.mk' K) x = (QuotientGroup.mk x : G ⧸ K) := rfl
    have h3 : (QuotientGroup.mk' K) g₀ = gbar := hg₀
    rw [h3, h2]
    exact hi
  -- `n = [G : K]` and `g₀ ^ n ∈ K`
  obtain ⟨n, hnord⟩ : ∃ n, orderOf ((QuotientGroup.mk' K) g₀) = n := ⟨_, rfl⟩
  have hn : 0 < n := by rw [← hnord]; exact orderOf_pos _
  have hk : g₀ ^ (n : ℤ) ∈ K := by
    have hpow : ((QuotientGroup.mk' K) g₀) ^ n = 1 := by
      rw [← hnord]; exact pow_orderOf_eq_one _
    have h1 : (QuotientGroup.mk' K) (g₀ ^ n) = 1 := by rw [map_pow]; exact hpow
    have h2 : g₀ ^ n ∈ K := (QuotientGroup.eq_one_iff (g₀ ^ n)).mp h1
    simpa using h2
  -- the `g₀`-conjugate representation has the same character as `W.ρ`
  have hchainv : Work.Clifford.conjFun K g₀ ψ = ψ := by
    have hmem : g₀ ∈ Work.Clifford.inertia K ψ := by rw [hinv]; exact Subgroup.mem_top g₀
    exact (Work.Clifford.mem_inertia K ψ g₀).mp hmem
  have hchar' : Representation.character (ρ.comp (conjAut K g₀).toMonoidHom)
      = Representation.character ρ := by
    funext k
    show ρ.character (conjAut K g₀ k) = ρ.character k
    rw [hρchar, ← conjFun_eq_apply_conjAut (K := K) g₀ ψ k, hchainv]
  -- an intertwining linear equivalence `P₀`
  obtain ⟨φ⟩ := nonempty_equiv_of_char_eq hρirr hchar'.symm
  obtain ⟨P, hP, hPn⟩ :=
    exists_normalized_intertwiner ρ hρirr g₀ n hk φ.toLinearEquiv
      (fun k => φ.isIntertwining' k)
  obtain ⟨R, hRirr, hRK⟩ :=
    exists_extension_rep ρ hρirr g₀ n hn hgen hnord hk P hP hPn
  refine ⟨R.character, Work.CharCore.irreducible_character_mem_Irr R hRirr, ?_⟩
  have hRk : ∀ k : ↥K, R (k : G) = ρ k := fun k => by
    simpa using DFunLike.congr_fun hRK k
  rw [Work.Clifford.Extends]
  funext k
  change LinearMap.trace ℂ ↥W (R (k : G)) = ψ k
  rw [hRk k]
  change Representation.character ρ k = ψ k
  rw [hρchar]

end Work.CharPrelim

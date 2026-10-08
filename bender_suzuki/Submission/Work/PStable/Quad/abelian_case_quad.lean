import Mathlib
import Submission.Work.PStable.Quad.Defs
import Submission.Work.HallHigman.GLCore.Defs
import Submission.Work.HallHigman.GLCore.abelian_case
import Submission.Work.PStable.abelian_centralized_of_quadratic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PStable.Quad

set_option linter.style.haveILetI false

open Work.HallHigman.GLCore

/-- The abelian GL-core in the "quadratic" setting: `𝒬` abelian, finite, of order prime to `p`,
`X` of order `p` normalising `𝒬` and not commuting with it, and `V` irreducible for `𝒬 ∪ {X}`
imply `(X - 1) ^ (p - 1) ≠ 0`.

This is the same weight-space-shift argument as `Work.HallHigman.GLCore.abelian_case`, but the
oddness of `|𝒬|` is never used by that argument, so the `CoreHyp` hypothesis may be replaced by the
weaker `QuadCore` data (`finite`, `cop`, `pow`, `norm`, `noncomm` all have the same field names). -/
lemma abelian_quad_core {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [IsAlgClosed K] [FiniteDimensional K V] {p : ℕ} [Fact p.Prime] [CharP K p]
    {Q : Subgroup (Module.End K V)ˣ} {X : (Module.End K V)ˣ}
    (h : Work.PStable.Quad.QuadCore p Q X) (hab : IsMulCommutative Q)
    (hirr : Work.HallHigman.IsIrreducibleFor
      ((fun a : (Module.End K V)ˣ => (a : Module.End K V)) '' (Q ∪ {X}))) :
    ((X : Module.End K V) - 1) ^ (p - 1) ≠ 0 := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Finite Q := h.finite
  haveI : Fintype Q := Fintype.ofFinite Q
  haveI : Nontrivial V := hirr.1
  have hcardK : (Nat.card Q : K) ≠ 0 := by
    intro hc
    exact h.cop ((CharP.cast_eq_zero_iff K p (Nat.card Q)).mp hc)
  let ρ : Q →* Module.End K V := (Units.coeHom (Module.End K V)).comp Q.subtype
  have hρ : ∀ a : Q, ρ a = ((a : (Module.End K V)ˣ) : Module.End K V) := fun a => rfl
  have hcomm : ∀ a b : Q, a * b = b * a := fun a b => hab.is_comm.comm a b
  obtain ⟨χ, v, hv, hχv⟩ := exists_common_eigenvector ρ hcomm
  have hχne : ∀ a : Q, χ a ≠ 0 := by
    intro a h0
    have h1 : (χ a) * (χ a⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [h0, zero_mul] at h1
    exact one_ne_zero h1.symm
  -- conjugation by powers of `X` preserves `Q`
  have hconj : ∀ k : ℕ, ∀ a ∈ Q, X ^ k * a * (X ^ k)⁻¹ ∈ Q := by
    intro k
    induction k with
    | zero => intro a ha; simpa using ha
    | succ k ih =>
      intro a ha
      have hb : X ^ k * a * (X ^ k)⁻¹ ∈ Q := ih a ha
      have hc := h.norm _ hb
      simpa [show X ^ (k + 1) * a * (X ^ (k + 1))⁻¹
          = X * (X ^ k * a * (X ^ k)⁻¹) * X⁻¹ from by group] using hc
  have hnorm_inv : ∀ a ∈ Q, X⁻¹ * a * X ∈ Q := by
    intro a ha
    have h1 : X ^ (p - 1) * a * (X ^ (p - 1))⁻¹ ∈ Q := hconj (p - 1) a ha
    have hXp : X ^ (p - 1) = X⁻¹ := by
      have h2 : X ^ (p - 1) * X = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel hp.one_le, h.pow]
      calc X ^ (p - 1) = X ^ (p - 1) * 1 := (mul_one _).symm
        _ = X ^ (p - 1) * (X * X⁻¹) := by rw [mul_inv_cancel]
        _ = X ^ (p - 1) * X * X⁻¹ := by rw [mul_assoc]
        _ = 1 * X⁻¹ := by rw [h2]
        _ = X⁻¹ := one_mul _
    have h4 : (X ^ (p - 1))⁻¹ = X := by rw [hXp, inv_inv]
    rwa [h4, hXp] at h1
  -- conjugation by `X⁻¹` as an endomorphism of `Q`
  let γ : Monoid.End Q :=
    { toFun := fun a => ⟨X⁻¹ * (a : (Module.End K V)ˣ) * X, hnorm_inv a a.2⟩
      map_one' := by
        apply Subtype.ext
        show X⁻¹ * (1 : (Module.End K V)ˣ) * X = 1
        group
      map_mul' := by
        intro a b
        apply Subtype.ext
        show X⁻¹ * (((a * b : Q)) : (Module.End K V)ˣ) * X
            = (X⁻¹ * (a : (Module.End K V)ˣ) * X) * (X⁻¹ * (b : (Module.End K V)ˣ) * X)
        rw [Subgroup.coe_mul]
        group }
  have hγcoe : ∀ (i : ℕ) (a : Q),
      (((γ ^ i) a : Q) : (Module.End K V)ˣ) = (X ^ i)⁻¹ * (a : (Module.End K V)ˣ) * X ^ i := by
    intro i
    induction i with
    | zero => intro a; simp
    | succ i ih =>
      intro a
      have h1 : (γ ^ (i + 1)) a = (γ ^ i) (γ a) := by
        rw [pow_succ]
        simp
      rw [h1, ih (γ a)]
      have h2 : ((γ a : Q) : (Module.End K V)ˣ) = X⁻¹ * (a : (Module.End K V)ˣ) * X := rfl
      rw [h2]
      group
  have hγp : γ ^ p = 1 := by
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    have hcoe := hγcoe p a
    rw [h.pow, inv_one, one_mul, mul_one] at hcoe
    exact hcoe
  have hstepU : ∀ c : Q,
      (c : (Module.End K V)ˣ) * X = X * ((γ c : Q) : (Module.End K V)ˣ) := by
    intro c
    have hc : ((γ c : Q) : (Module.End K V)ˣ) = X⁻¹ * (c : (Module.End K V)ˣ) * X := rfl
    rw [hc]
    group
  have hstep : ∀ c : Q, ρ c * (X : Module.End K V) = (X : Module.End K V) * ρ (γ c) := by
    intro c
    have h := congrArg (fun u : (Module.End K V)ˣ => (u : Module.End K V)) (hstepU c)
    simp only [Units.val_mul] at h
    rw [hρ c, hρ (γ c)]
    exact h
  have hop : ∀ (i : ℕ) (a : Q), ρ a * (X : Module.End K V) ^ i
      = (X : Module.End K V) ^ i * ρ ((γ ^ i) a) := by
    intro i
    induction i with
    | zero => intro a; simp
    | succ i ih =>
      intro a
      have h1 : (γ ^ (i + 1)) a = γ ((γ ^ i) a) := by
        rw [pow_succ']
        rfl
      calc ρ a * (X : Module.End K V) ^ (i + 1)
          = ρ a * ((X : Module.End K V) ^ i * (X : Module.End K V)) := by rw [pow_succ]
        _ = (ρ a * (X : Module.End K V) ^ i) * (X : Module.End K V) := by rw [mul_assoc]
        _ = ((X : Module.End K V) ^ i * ρ ((γ ^ i) a)) * (X : Module.End K V) := by rw [ih a]
        _ = (X : Module.End K V) ^ i * (ρ ((γ ^ i) a) * (X : Module.End K V)) := by
              rw [mul_assoc]
        _ = (X : Module.End K V) ^ i
              * ((X : Module.End K V) * ρ (γ ((γ ^ i) a))) := by rw [hstep ((γ ^ i) a)]
        _ = ((X : Module.End K V) ^ i * (X : Module.End K V))
              * ρ (γ ((γ ^ i) a)) := by rw [mul_assoc]
        _ = (X : Module.End K V) ^ (i + 1) * ρ ((γ ^ (i + 1)) a) := by rw [pow_succ, h1]
  have hwt : ∀ (i : ℕ) (a : Q), ρ a (((X : Module.End K V) ^ i) v)
      = χ ((γ ^ i) a) • (((X : Module.End K V) ^ i) v) := by
    intro i a
    calc ρ a (((X : Module.End K V) ^ i) v)
        = (ρ a * (X : Module.End K V) ^ i) v :=
            (Module.End.mul_apply (ρ a) ((X : Module.End K V) ^ i) v).symm
      _ = ((X : Module.End K V) ^ i * ρ ((γ ^ i) a)) v := by rw [hop i a]
      _ = ((X : Module.End K V) ^ i) (ρ ((γ ^ i) a) v) :=
            Module.End.mul_apply ((X : Module.End K V) ^ i) (ρ ((γ ^ i) a)) v
      _ = ((X : Module.End K V) ^ i) (χ ((γ ^ i) a) • v) := by rw [hχv]
      _ = χ ((γ ^ i) a) • (((X : Module.End K V) ^ i) v) :=
            map_smul ((X : Module.End K V) ^ i) (χ ((γ ^ i) a)) v
  by_cases hcase : ∀ a : Q, χ (γ a) = χ a
  · -- the weight is `X`-stable: the weight space is invariant, hence all of `V`
    exfalso
    set Vχ : Submodule K V := ⨅ a : Q, Module.End.eigenspace (ρ a) (χ a) with hVχdef
    have hmem : ∀ w : V, w ∈ Vχ ↔ ∀ a : Q, ρ a w = χ a • w := by
      intro w
      rw [hVχdef, Submodule.mem_iInf]
      exact forall_congr' (fun a => Module.End.mem_eigenspace_iff)
    have hvVχ : v ∈ Vχ := by rw [hmem]; exact hχv
    have hne : Vχ ≠ ⊥ := by
      intro hbot
      have hmem0 : v ∈ (⊥ : Submodule K V) := hbot ▸ hvVχ
      rw [Submodule.mem_bot] at hmem0
      exact hv hmem0
    have hinv : ∀ s ∈ ((fun a : (Module.End K V)ˣ => (a : Module.End K V)) '' (Q ∪ {X})),
        Vχ ≤ Vχ.comap s := by
      intro s hs w hw
      rw [Submodule.mem_comap]
      rw [hmem w] at hw
      rw [hmem (s w)]
      rcases hs with ⟨u, hu, rfl⟩
      rcases hu with hu | hu
      · intro b
        have hρu : ρ ⟨u, hu⟩ = (u : Module.End K V) := by rw [hρ]
        have hcomm' : ρ b * ρ ⟨u, hu⟩ = ρ ⟨u, hu⟩ * ρ b := by
          rw [← map_mul, ← map_mul, hcomm b ⟨u, hu⟩]
        calc ρ b ((u : Module.End K V) w) = (ρ b * ρ ⟨u, hu⟩) w := by
              rw [hρu, Module.End.mul_apply]
          _ = (ρ ⟨u, hu⟩ * ρ b) w := by rw [hcomm']
          _ = ρ ⟨u, hu⟩ (ρ b w) := rfl
          _ = ρ ⟨u, hu⟩ (χ b • w) := by rw [hw b]
          _ = χ b • ρ ⟨u, hu⟩ w := map_smul (ρ ⟨u, hu⟩) (χ b) w
          _ = χ b • (u : Module.End K V) w := by rw [hρu]
      · intro b
        have huX : (u : (Module.End K V)ˣ) = X := hu
        rw [huX]
        calc ρ b ((X : Module.End K V) w) = (ρ b * (X : Module.End K V)) w := rfl
          _ = ((X : Module.End K V) * ρ (γ b)) w := by rw [hstep b]
          _ = (X : Module.End K V) (ρ (γ b) w) := rfl
          _ = (X : Module.End K V) (χ (γ b) • w) := by rw [hw (γ b)]
          _ = χ (γ b) • (X : Module.End K V) w := map_smul _ _ _
          _ = χ b • (X : Module.End K V) w := by rw [hcase b]
    rcases hirr.2 Vχ hinv with hb | ht
    · exact hne hb
    · have hscal : ∀ a : Q, ρ a = χ a • (1 : Module.End K V) := by
        intro a
        ext w
        have hw : w ∈ Vχ := by rw [ht]; exact Submodule.mem_top
        simpa using (hmem w).mp hw a
      obtain ⟨a, haQ, hnc⟩ := h.noncomm
      exact hnc (by
        apply Units.ext
        calc (a : Module.End K V) * (X : Module.End K V)
            = ρ ⟨a, haQ⟩ * (X : Module.End K V) := by rw [hρ]
          _ = (χ ⟨a, haQ⟩ • (1 : Module.End K V)) * (X : Module.End K V) := by
                rw [hscal ⟨a, haQ⟩]
          _ = χ ⟨a, haQ⟩ • (X : Module.End K V) := by rw [smul_mul_assoc, one_mul]
          _ = (X : Module.End K V) * (χ ⟨a, haQ⟩ • (1 : Module.End K V)) := by
                rw [mul_smul_comm, mul_one]
          _ = (X : Module.End K V) * ρ ⟨a, haQ⟩ := by rw [hscal ⟨a, haQ⟩]
          _ = (X : Module.End K V) * (a : Module.End K V) := by rw [hρ])
  · -- the weight is not `X`-stable: the projector separates the weight spaces
    set P : Module.End K V := (Nat.card Q : K)⁻¹ • ∑ a : Q, (χ a)⁻¹ • ρ a with hPdef
    have hPsum : ∀ w : V, P w = (Nat.card Q : K)⁻¹ • ∑ a : Q, (χ a)⁻¹ • (ρ a w) := by
      intro w
      rw [hPdef, LinearMap.smul_apply, LinearMap.sum_apply]
      exact congrArg _ (Finset.sum_congr rfl (fun a _ => LinearMap.smul_apply _ _ _))
    have hPv : P v = v := by
      rw [hPsum]
      have h1 : (∑ a : Q, (χ a)⁻¹ • (ρ a v)) = (Nat.card Q : K) • v := by
        rw [Finset.sum_congr rfl (fun a _ => by
              rw [hχv a, smul_smul, inv_mul_cancel₀ (hχne a), one_smul]),
          Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K (Fintype.card Q) v,
          Nat.card_eq_fintype_card]
      rw [h1, smul_smul, inv_mul_cancel₀ hcardK, one_smul]
    have hP0 : ∀ (ψ : Q →* K) (w : V), ψ ≠ χ → (∀ a : Q, ρ a w = ψ a • w) → P w = 0 := by
      intro ψ w hneψ hw
      let δ : Q →* K :=
        { toFun := fun a => (χ a)⁻¹ * ψ a
          map_one' := by simp
          map_mul' := by
            intro a b
            simp only [map_mul]
            rw [mul_inv_rev]
            ring }
      have hδne : δ ≠ 1 := by
        intro h1
        apply hneψ
        apply MonoidHom.ext
        intro a
        have h2 : (χ a)⁻¹ * ψ a = 1 := by
          have h1a := (MonoidHom.ext_iff.mp h1) a
          simpa [δ] using h1a
        calc ψ a = χ a * ((χ a)⁻¹ * ψ a) := by
              rw [← mul_assoc, mul_inv_cancel₀ (hχne a), one_mul]
          _ = χ a := by rw [h2, mul_one]
      have hsum0 : (∑ a : Q, δ a) = 0 := sum_hom_units_eq_zero δ hδne
      have h1 : (∑ a : Q, (χ a)⁻¹ • (ρ a w)) = ∑ a : Q, δ a • w := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [hw a, smul_smul]
        rfl
      rw [hPsum, h1, ← Finset.sum_smul, hsum0, zero_smul, smul_zero]
    have hγiter : ∀ i : ℕ, ∀ a : Q, ((γ : Q → Q)^[i]) a = (γ ^ i) a := by
      intro i a
      rw [← Monoid.End.coe_pow]
    have hγid : (γ : Q → Q)^[p] = id := by
      rw [← Monoid.End.coe_pow, hγp, Monoid.End.coe_one]
    have hPXi : ∀ i : ℕ, 0 < i → i < p → P (((X : Module.End K V) ^ i) v) = 0 := by
      intro i hi1 hip
      refine hP0 (χ.comp (γ ^ i)) _ ?_ (hwt i)
      intro hcontra
      apply hcase
      have hi : ∀ a : Q, χ (((γ : Q → Q)^[i]) a) = χ a := by
        intro a
        rw [hγiter i a]
        exact (MonoidHom.ext_iff.mp hcontra) a
      exact iterate_eq_of_iterate_eq hp (γ : Q → Q) hγid χ hi1 hip hi
    have hNv : (((X : Module.End K V) - 1) ^ (p - 1)) v ≠ 0 := by
      intro h0
      have hmap : P ((((X : Module.End K V) - 1) ^ (p - 1)) v)
          = ∑ i ∈ Finset.range p, P (((X : Module.End K V) ^ i) v) := by
        haveI : CharP (Module.End K V) p := charP_moduleEnd
        rw [sub_one_pow_pred_eq_sum, LinearMap.sum_apply, map_sum]
      have h2 : ∑ i ∈ Finset.range p, P (((X : Module.End K V) ^ i) v) = v := by
        rw [Finset.sum_eq_single 0]
        · simpa using hPv
        · intro i hi hir
          exact hPXi i (Nat.pos_of_ne_zero hir) (Finset.mem_range.mp hi)
        · intro hnot
          exact absurd (Finset.mem_range.mpr hp.pos) hnot
      have h1 : P ((((X : Module.End K V) - 1) ^ (p - 1)) v) = 0 := by rw [h0, map_zero]
      rw [hmap, h2] at h1
      exact hv h1
    intro hzero
    exact hNv (by rw [hzero]; simp)

theorem abelian_case_quad {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [IsAlgClosed K] [FiniteDimensional K V] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {Q : Subgroup (Module.End K V)ˣ} {X : (Module.End K V)ˣ}
    (h : Work.PStable.Quad.QuadCore p Q X) (hab : IsMulCommutative Q)
    (hirr : Work.HallHigman.IsIrreducibleFor
      ((fun a : (Module.End K V)ˣ => (a : Module.End K V)) '' (Q ∪ {X}))) :
    ((X : Module.End K V) - 1) ^ 2 ≠ 0 := by
  have hcore := abelian_quad_core h hab hirr
  intro hzero
  exact hcore (by
    have hp : p.Prime := Fact.out
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    rw [show p - 1 = 2 + (p - 3) by omega, pow_add, hzero, zero_mul])

end Work.PStable.Quad

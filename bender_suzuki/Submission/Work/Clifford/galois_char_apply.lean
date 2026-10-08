import Mathlib
import Submission.Work.Clifford.CFun
import Submission.Work.CharCore.star_trace_eq_trace_pow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.galois_char_apply`

The Galois (automorphism) action on irreducible characters of a finite group.

If `ζ` is a primitive `n`-th root of unity, `|G| ∣ n`, and `σ : ℂ ≃+* ℂ` is a ring
automorphism with `σ ζ = ζ ^ k`, then for every irreducible character `χ` of `G` and every
`g : G` one has `σ (χ g) = χ (g ^ k)`.

This is the standard statement that the Galois action on character values is given by the
power map on the underlying eigenvalues: the eigenvalues of `ρ g` for a representation
realising `χ` are `n`-th roots of unity, permuted by `σ` via `λ ↦ λ ^ k`, so `σ` acts on the
trace by replacing each eigenvalue `λ` by `λ ^ k`, i.e. by sending `trace (ρ g)` to
`trace ((ρ g) ^ k) = trace (ρ (g ^ k))`.

The linear-algebra input is the generalisation to an arbitrary automorphism `σ` of
`Work.CharCore.star_trace_eq_trace_pow` (the case of complex conjugation, `σ = star`,
`k = n - 1`); the proof follows the same induction on the dimension, replacing the argument
`star c = c ^ (n - 1)` by `σ c = c ^ k`, which holds because `c` is an `n`-th root of unity
and hence a power of `ζ`.
-/

noncomputable section

open Classical LinearMap

namespace Work.Clifford

open Work.CharCore (blk blk_apply blk_pow blk_trace blk_trace_pow)

universe u

/-- **Linear-algebra core of the Galois action on characters.**

Let `r ∣ n` with `n > 0`, let `ζ` be a primitive `n`-th root of unity and `σ : ℂ ≃+* ℂ`
with `σ ζ = ζ ^ k`.  Then for every endomorphism `T` of a finite dimensional complex vector
space with `T ^ r = 1` one has `σ (trace T) = trace (T ^ k)`.

The proof is a strong induction on `finrank ℂ V`: over `ℂ`, `T` has an eigenvector with
eigenvalue `c`, which satisfies `c ^ r = 1`, hence `c ^ n = 1`, hence `c = ζ ^ i` for some
`i`, and therefore `σ c = c ^ k`.  Completing `ℂ ∙ v` to a direct sum `V ≃ (ℂ ∙ v) × U`
writes `T` as a block upper triangular matrix, and the traces decompose; the endomorphism
`D := T|_U` again satisfies `D ^ r = 1` and the induction hypothesis applies to it. -/
theorem galois_trace_aux (r n k : ℕ) (hn0 : 0 < n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (hrn : r ∣ n) (σ : ℂ ≃+* ℂ) (hσ : σ ζ = ζ ^ k) :
    ∀ (d : ℕ), ∀ (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
      Module.finrank ℂ V = d →
      ∀ (T : V →ₗ[ℂ] V), T ^ r = 1 →
      σ (LinearMap.trace ℂ V T) = LinearMap.trace ℂ V (T ^ k) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro V _ _ _ hdim T hT
    by_cases hnt : Nontrivial V
    · haveI : Nontrivial V := hnt
      obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
      rw [Module.End.hasEigenvalue_iff] at hc
      obtain ⟨v, hv, hvne⟩ := (Submodule.ne_bot_iff _).mp hc
      have hTv : T v = c • v := Module.End.mem_eigenspace_iff.mp hv
      -- the line spanned by `v`
      set W : Submodule ℂ V := Submodule.span ℂ {v} with hWdef
      have hWfin : Module.finrank ℂ ↥W = 1 := finrank_span_singleton hvne
      -- `T` acts on `W` as multiplication by `c`
      have hTW_eq : ∀ x ∈ W, T x = c • x := by
        intro x hx
        have hvmem : v ∈ LinearMap.ker (T - c • (1 : V →ₗ[ℂ] V)) := by
          rw [LinearMap.mem_ker]
          rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hTv, sub_self]
        have hsub : W ≤ LinearMap.ker (T - c • (1 : V →ₗ[ℂ] V)) := by
          rw [hWdef]
          exact Submodule.span_le.mpr (fun y hy => by
            rw [Set.mem_singleton_iff] at hy
            subst hy
            exact hvmem)
        have hxker := hsub hx
        rw [LinearMap.mem_ker] at hxker
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hxker
        exact hxker
      have hTW : ∀ x ∈ W, T x ∈ W := fun x hx => by
        rw [hTW_eq x hx]; exact W.smul_mem c hx
      -- `c` is an `n`-th root of unity
      have hp : (T ^ r) v = c ^ r • v := by
        have h := Module.End.aeval_apply_of_mem_apply_eq_smul (p := Polynomial.X ^ r) hTv
        rwa [map_pow, Polynomial.aeval_X, Polynomial.eval_pow, Polynomial.eval_X] at h
      have hcr : c ^ r = 1 := by
        have hv_eq : v = c ^ r • v := by rw [← hp, hT, Module.End.one_apply]
        have hz : (c ^ r - 1) • v = 0 := by
          rw [sub_smul, one_smul, ← hv_eq, sub_self]
        rcases smul_eq_zero.mp hz with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hvne
      have hcn : c ^ n = 1 := by
        obtain ⟨m, hm⟩ := hrn
        rw [hm, pow_mul, hcr, one_pow]
      have hsigma_c : σ c = c ^ k := by
        haveI : NeZero n := ⟨hn0.ne'⟩
        obtain ⟨i, _hi, hieq⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hζ hcn
        rw [← hieq]
        calc σ (ζ ^ i) = (σ ζ) ^ i := map_pow σ ζ i
          _ = (ζ ^ k) ^ i := by rw [hσ]
          _ = ζ ^ (k * i) := by rw [pow_mul]
          _ = ζ ^ (i * k) := by rw [mul_comm]
          _ = (ζ ^ i) ^ k := by rw [pow_mul]
      -- complement and block decomposition
      obtain ⟨U, hcompl⟩ := Submodule.exists_isCompl W
      set Φ : (↥W × ↥U) ≃ₗ[ℂ] V := Submodule.prodEquivOfIsCompl W U hcompl with hΦ
      set e : V ≃ₗ[ℂ] ↥W × ↥U := Φ.symm with he
      set T' : ↥W × ↥U →ₗ[ℂ] ↥W × ↥U := (e.conjAlgEquiv ℂ) T with hT'def
      set πW : V →ₗ[ℂ] ↥W :=
        (LinearMap.fst ℂ ↥W ↥U).comp (e : V →ₗ[ℂ] ↥W × ↥U) with hπW
      set πU : V →ₗ[ℂ] ↥U :=
        (LinearMap.snd ℂ ↥W ↥U).comp (e : V →ₗ[ℂ] ↥W × ↥U) with hπU
      set A : ↥W →ₗ[ℂ] ↥W := πW.comp (T.comp W.subtype) with hA
      set B : ↥U →ₗ[ℂ] ↥W := πW.comp (T.comp U.subtype) with hB
      set D : ↥U →ₗ[ℂ] ↥U := πU.comp (T.comp U.subtype) with hD
      have he_W : ∀ x : ↥W, e (x : V) = (x, 0) :=
        fun x => Submodule.prodEquivOfIsCompl_symm_apply_left W U hcompl x
      have hconjAlg : ∀ f : V →ₗ[ℂ] V, e.conj f = (e.conjAlgEquiv ℂ) f := by
        intro f
        rw [LinearEquiv.conjAlgEquiv_apply, LinearEquiv.conj_apply]; rfl
      have hT'conj : e.conj T = T' := by
        rw [hT'def]; exact hconjAlg T
      have hπW_W : ∀ x : ↥W, πW (x : V) = x := by
        intro x
        simp only [hπW, LinearMap.comp_apply, LinearMap.fst_apply]
        exact congrArg Prod.fst (he_W x)
      have hT'apply : ∀ (w : ↥W) (u : ↥U), T' (w, u) = e (T (e.symm (w, u))) := by
        intro w u
        rw [hT'def, LinearEquiv.conjAlgEquiv_apply]
        rfl
      have hBD : ∀ u : ↥U, e (T (u : V)) = (B u, D u) := by
        intro u
        apply Prod.ext
        · simp only [hB, hπW, LinearMap.comp_apply, LinearMap.fst_apply, Submodule.subtype_apply]
          rfl
        · simp only [hD, hπU, LinearMap.comp_apply, LinearMap.snd_apply, Submodule.subtype_apply]
          rfl
      have hAw : ∀ w : ↥W, A w = ⟨T (w : V), hTW (w : V) w.2⟩ := by
        intro w
        simp only [hA, hπW, LinearMap.comp_apply, LinearMap.fst_apply, Submodule.subtype_apply]
        exact congrArg Prod.fst (he_W ⟨T (w : V), hTW (w : V) w.2⟩)
      have hT'blk : T' = blk A B D := by
        apply LinearMap.ext
        rintro ⟨w, u⟩
        have hsymm : (e.symm (w, u) : V) = (w : V) + (u : V) :=
          Submodule.coe_prodEquivOfIsCompl' W U hcompl (w, u)
        rw [hT'apply w u, hsymm, map_add, map_add,
          he_W ⟨T (w : V), hTW (w : V) w.2⟩, hBD u, blk_apply, hAw w]
        simp
      -- `D ^ r = 1`
      have hT'r : T' ^ r = 1 := by
        have h := map_pow (e.conjAlgEquiv ℂ) T r
        rw [hT, map_one] at h
        rw [← hT'def] at h
        exact h.symm
      have hDr : D ^ r = 1 := by
        obtain ⟨B'', hB''⟩ := blk_pow A B D r
        have h2 : blk (A ^ r) B'' (D ^ r) = 1 := by rw [← hB'', ← hT'blk, hT'r]
        apply LinearMap.ext
        intro u
        have h3 := congrArg (fun f : ↥W × ↥U →ₗ[ℂ] ↥W × ↥U => (f (0, u)).2) h2
        simpa [blk_apply, Module.End.one_apply] using h3
      -- dimension count
      have hfin : Module.finrank ℂ ↥U < d := by
        have h1 : Module.finrank ℂ V = Module.finrank ℂ ↥W + Module.finrank ℂ ↥U := by
          rw [LinearEquiv.finrank_eq e, Module.finrank_prod]
        omega
      -- traces
      have hA_scalar : A = c • (1 : ↥W →ₗ[ℂ] ↥W) := by
        apply LinearMap.ext
        intro w
        rw [LinearMap.smul_apply, Module.End.one_apply]
        change πW (T ((w : V))) = c • w
        rw [hTW_eq (w : V) w.2, map_smul, hπW_W w]
      have hApow_eq : ∀ j : ℕ, A ^ j = c ^ j • (1 : ↥W →ₗ[ℂ] ↥W) := by
        intro j
        rw [hA_scalar]
        conv_lhs => rw [← Algebra.algebraMap_eq_smul_one]
        conv_rhs => rw [← Algebra.algebraMap_eq_smul_one]
        rw [← map_pow]
      have hApow_trace : ∀ j : ℕ, LinearMap.trace ℂ ↥W (A ^ j) = c ^ j := by
        intro j
        rw [hApow_eq j, map_smul, LinearMap.trace_one, hWfin]
        simp
      have hA1 : LinearMap.trace ℂ ↥W A = c := by simpa using hApow_trace 1
      have hIH : σ (LinearMap.trace ℂ ↥U D) = LinearMap.trace ℂ ↥U (D ^ k) :=
        ih (Module.finrank ℂ ↥U) hfin ↥U rfl D hDr
      have htrT : LinearMap.trace ℂ V T = LinearMap.trace ℂ ↥W A + LinearMap.trace ℂ ↥U D := by
        rw [← trace_conj' T e, hT'conj, hT'blk]
        exact blk_trace A B D
      have htrTp : LinearMap.trace ℂ V (T ^ k) =
          LinearMap.trace ℂ ↥W (A ^ k) + LinearMap.trace ℂ ↥U (D ^ k) := by
        have hpow : e.conj (T ^ k) = (e.conj T) ^ k := by
          rw [hconjAlg, hconjAlg]
          exact map_pow (e.conjAlgEquiv ℂ) T k
        rw [← trace_conj' (T ^ k) e, hpow, hT'conj, hT'blk]
        exact blk_trace_pow A B D k
      rw [htrT, htrTp, hA1, map_add, hIH, hApow_trace k, hsigma_c]
    · haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hnt
      have h1 : T = 0 := LinearMap.ext fun x => Subsingleton.elim (T x) 0
      have h2 : T ^ k = 0 := LinearMap.ext fun x => Subsingleton.elim _ _
      rw [h2, h1]
      simp

/-- **The Galois action on irreducible characters.**

Let `ζ` be a primitive `n`-th root of unity, `|G| ∣ n`, and `σ : ℂ ≃+* ℂ` with
`σ ζ = ζ ^ k`.  Then for every irreducible character `χ` of `G` and every `g : G`,
`σ (χ g) = χ (g ^ k)`. -/
theorem galois_char_apply {G : Type*} [Group G] [Fintype G] {n : ℕ} (hn0 : 0 < n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (hn : Nat.card G ∣ n) (σ : ℂ ≃+* ℂ) {k : ℕ} (hσ : σ ζ = ζ ^ k)
    {χ : G → ℂ} (hχ : χ ∈ Work.Clifford.Irr G) (g : G) :
    σ (χ g) = χ (g ^ k) := by
  obtain ⟨V, _hVsimple, hVχ⟩ := (Work.Clifford.mem_Irr (G := G) (χ := χ)).mp hχ
  have hcard : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨1⟩
  have hrn : Fintype.card G ∣ n := by rwa [Fintype.card_eq_nat_card]
  have hT : (V.ρ g) ^ (Fintype.card G) = 1 := by
    rw [← map_pow, pow_card_eq_one, map_one]
  have hmain := galois_trace_aux (Fintype.card G) n k hn0 hζ hrn σ hσ
    (Module.finrank ℂ V) V rfl (V.ρ g) hT
  rw [← hVχ]
  show σ (LinearMap.trace ℂ V (V.ρ g)) = LinearMap.trace ℂ V (V.ρ (g ^ k))
  rw [map_pow]
  exact hmain

end Work.Clifford

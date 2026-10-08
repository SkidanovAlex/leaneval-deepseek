import Mathlib
import Submission.Work.CharCore.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharCore.star_trace_eq_trace_pow`

If `T : V →ₗ[ℂ] V` is an endomorphism of a finite dimensional complex vector space
with `T ^ n = 1` (`n > 0`), then `T` is invertible with inverse `T ^ (n - 1)`, and
its trace satisfies

`starRingEnd ℂ (trace T) = trace (T ^ (n - 1))`.

This is the fact that for a finite order element the trace of the inverse is the
complex conjugate of the trace (all eigenvalues are roots of unity).

The proof runs by induction on `finrank ℂ V`.  Over ℂ an endomorphism of a
nontrivial finite dimensional space has an eigenvector `v`, with eigenvalue `c`
satisfying `c ^ n = 1`, hence `star c = c ^ (n - 1)`.  Completing `ℂ ∙ v` to a
direct sum decomposition `V ≃ (ℂ ∙ v) × U` writes `T` as a block upper triangular
matrix, so the traces decompose; `D := T|_U` again satisfies `D ^ n = 1` and the
induction hypothesis applies to `U`, which is one dimension smaller.
-/

noncomputable section

open LinearMap

namespace Work.CharCore

/-- The block upper triangular endomorphism `(w, u) ↦ (A w + B u, D u)` of `W × U`. -/
def blk {W U : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    (A : W →ₗ[ℂ] W) (B : U →ₗ[ℂ] W) (D : U →ₗ[ℂ] U) : W × U →ₗ[ℂ] W × U :=
  LinearMap.prod (A.comp (LinearMap.fst ℂ W U) + B.comp (LinearMap.snd ℂ W U))
                 (D.comp (LinearMap.snd ℂ W U))

@[simp] theorem blk_apply {W U : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    (A : W →ₗ[ℂ] W) (B : U →ₗ[ℂ] W) (D : U →ₗ[ℂ] U) (w : W) (u : U) :
    blk A B D (w, u) = (A w + B u, D u) := by
  simp [blk]

theorem blk_comp {W U : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    (A₁ : W →ₗ[ℂ] W) (B₁ : U →ₗ[ℂ] W) (D₁ : U →ₗ[ℂ] U)
    (A₂ : W →ₗ[ℂ] W) (B₂ : U →ₗ[ℂ] W) (D₂ : U →ₗ[ℂ] U) :
    blk A₁ B₁ D₁ * blk A₂ B₂ D₂ =
      blk (A₁ * A₂) (A₁.comp B₂ + B₁.comp D₂) (D₁ * D₂) := by
  apply LinearMap.ext
  rintro ⟨w, u⟩
  simp only [Module.End.mul_apply, LinearMap.comp_apply, blk_apply, LinearMap.add_apply, map_add]
  rw [Prod.mk.injEq]
  exact ⟨by abel, rfl⟩

theorem blk_pow {W U : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    (A : W →ₗ[ℂ] W) (B : U →ₗ[ℂ] W) (D : U →ₗ[ℂ] U) (k : ℕ) :
    ∃ B' : U →ₗ[ℂ] W, (blk A B D) ^ k = blk (A ^ k) B' (D ^ k) := by
  induction k with
  | zero => exact ⟨0, by apply LinearMap.ext; rintro ⟨w, u⟩; simp [blk]⟩
  | succ k ih =>
    obtain ⟨B', hB'⟩ := ih
    exact ⟨(A ^ k).comp B + B'.comp D, by
      rw [pow_succ, hB', blk_comp]
      simp only [pow_succ]⟩

theorem blk_trace {W U : Type*} [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Module.Free ℂ W]
    [AddCommGroup U] [Module ℂ U] [Module.Finite ℂ U] [Module.Free ℂ U]
    (A : W →ₗ[ℂ] W) (B : U →ₗ[ℂ] W) (D : U →ₗ[ℂ] U) :
    LinearMap.trace ℂ (W × U) (blk A B D) = LinearMap.trace ℂ W A + LinearMap.trace ℂ U D := by
  have hN : IsNilpotent (blk (0 : W →ₗ[ℂ] W) B (0 : U →ₗ[ℂ] U)) := by
    refine ⟨2, ?_⟩
    rw [pow_two]
    apply LinearMap.ext
    rintro ⟨w, u⟩
    simp [blk]
  have hdec : blk A B D = (A.prodMap D) + blk (0 : W →ₗ[ℂ] W) B (0 : U →ₗ[ℂ] U) := by
    apply LinearMap.ext
    rintro ⟨w, u⟩
    simp [blk]
  rw [hdec, map_add, trace_prodMap', (isNilpotent_trace_of_isNilpotent hN).eq_zero, add_zero]

theorem blk_trace_pow {W U : Type*} [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Module.Free ℂ W]
    [AddCommGroup U] [Module ℂ U] [Module.Finite ℂ U] [Module.Free ℂ U]
    (A : W →ₗ[ℂ] W) (B : U →ₗ[ℂ] W) (D : U →ₗ[ℂ] U) (k : ℕ) :
    LinearMap.trace ℂ (W × U) ((blk A B D) ^ k) =
      LinearMap.trace ℂ W (A ^ k) + LinearMap.trace ℂ U (D ^ k) := by
  obtain ⟨B', hB'⟩ := blk_pow A B D k
  rw [hB', blk_trace]

/-- Auxiliary statement, by strong induction on the dimension. -/
theorem star_trace_eq_trace_pow_aux :
    ∀ (d : ℕ), ∀ (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
      Module.finrank ℂ V = d →
      ∀ (T : V →ₗ[ℂ] V) (n : ℕ), 0 < n → T ^ n = 1 →
      starRingEnd ℂ (LinearMap.trace ℂ V T) = LinearMap.trace ℂ V (T ^ (n - 1)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro V _ _ _ hdim T n hn hT
    by_cases hnt : Nontrivial V
    · haveI : Nontrivial V := hnt
      -- an eigenvector
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
      -- `c` is a root of unity
      have hp : (T ^ n) v = c ^ n • v := by
        have h := Module.End.aeval_apply_of_mem_apply_eq_smul (p := Polynomial.X ^ n) hTv
        rwa [map_pow, Polynomial.aeval_X, Polynomial.eval_pow, Polynomial.eval_X] at h
      have hcn : c ^ n = 1 := by
        have hv_eq : v = c ^ n • v := by rw [← hp, hT, Module.End.one_apply]
        have hz : (c ^ n - 1) • v = 0 := by
          rw [sub_smul, one_smul, ← hv_eq, sub_self]
        rcases smul_eq_zero.mp hz with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hvne
      have hstar_c : starRingEnd ℂ c = c ^ (n - 1) := by
        have hc0 : c ≠ 0 := by
          intro h0
          rw [h0, zero_pow hn.ne'] at hcn
          exact zero_ne_one hcn
        have hnorm : ‖c‖ = 1 := by
          have h1 : ‖c ^ n‖ = 1 := by rw [hcn, norm_one]
          rw [norm_pow] at h1
          exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) hn.ne').mp h1
        have hinv : starRingEnd ℂ c = c⁻¹ := (Complex.inv_eq_conj hnorm).symm
        have hpow : c ^ (n - 1) = c⁻¹ := by
          have h2 : c ^ (n - 1) * c = 1 := by
            rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n), hcn]
          exact (mul_eq_one_iff_eq_inv₀ hc0).mp h2
        rw [hinv, hpow]
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
      -- `D ^ n = 1`
      have hT'n : T' ^ n = 1 := by
        have h := map_pow (e.conjAlgEquiv ℂ) T n
        rw [hT, map_one] at h
        rw [← hT'def] at h
        exact h.symm
      have hDn : D ^ n = 1 := by
        obtain ⟨B'', hB''⟩ := blk_pow A B D n
        have h2 : blk (A ^ n) B'' (D ^ n) = 1 := by rw [← hB'', ← hT'blk, hT'n]
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
      have hApow_eq : ∀ k : ℕ, A ^ k = c ^ k • (1 : ↥W →ₗ[ℂ] ↥W) := by
        intro k
        rw [hA_scalar]
        conv_lhs => rw [← Algebra.algebraMap_eq_smul_one]
        conv_rhs => rw [← Algebra.algebraMap_eq_smul_one]
        rw [← map_pow]
      have hApow_trace : ∀ k : ℕ, LinearMap.trace ℂ ↥W (A ^ k) = c ^ k := by
        intro k
        rw [hApow_eq k, map_smul, LinearMap.trace_one, hWfin]
        simp
      have hA1 : LinearMap.trace ℂ ↥W A = c := by simpa using hApow_trace 1
      have hIH : starRingEnd ℂ (LinearMap.trace ℂ ↥U D) =
          LinearMap.trace ℂ ↥U (D ^ (n - 1)) :=
        ih (Module.finrank ℂ ↥U) hfin ↥U rfl D n hn hDn
      have htrT : LinearMap.trace ℂ V T = LinearMap.trace ℂ ↥W A + LinearMap.trace ℂ ↥U D := by
        rw [← trace_conj' T e, hT'conj, hT'blk]
        exact blk_trace A B D
      have htrTp : LinearMap.trace ℂ V (T ^ (n - 1)) =
          LinearMap.trace ℂ ↥W (A ^ (n - 1)) + LinearMap.trace ℂ ↥U (D ^ (n - 1)) := by
        have hpow : e.conj (T ^ (n - 1)) = (e.conj T) ^ (n - 1) := by
          rw [hconjAlg, hconjAlg]
          exact map_pow (e.conjAlgEquiv ℂ) T (n - 1)
        rw [← trace_conj' (T ^ (n - 1)) e, hpow, hT'conj, hT'blk]
        exact blk_trace_pow A B D (n - 1)
      rw [htrT, htrTp, hA1, map_add, hIH, hApow_trace (n - 1), hstar_c]
    · haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hnt
      have h1 : T = 0 := LinearMap.ext fun x => Subsingleton.elim (T x) 0
      have h2 : T ^ (n - 1) = 0 := LinearMap.ext fun x => Subsingleton.elim _ _
      rw [h2, h1]
      simp

/-- The requested statement. -/
theorem star_trace_eq_trace_pow {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : V →ₗ[ℂ] V) (n : ℕ) (hn : 0 < n) (hT : T ^ n = 1) :
    starRingEnd ℂ (LinearMap.trace ℂ V T) = LinearMap.trace ℂ V (T ^ (n - 1)) :=
  star_trace_eq_trace_pow_aux (Module.finrank ℂ V) V rfl T n hn hT

end Work.CharCore

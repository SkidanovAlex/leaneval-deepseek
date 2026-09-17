import Mathlib
import Submission.Commons.Algebra.Lie.e8_finrank
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_zero_weightSpace_finrank
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_root_weightSpace_finrank_eq_one
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_weightSpace_reflect_finrank
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_simple_root_weightSpace_finrank_compat
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_serreE_ne_zero
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_norm_two_conj_simple
import Submission.Commons.LinearAlgebra.Eigenvector.linearIndependent_of_separating_eigenvalues

open CartanMatrix

namespace Commons.Algebra.Lie.SerreConstruction
open Commons.Algebra.Lie

noncomputable section

/-- The Serre-constructed `e₈` is finite-dimensional (it has dimension `248`).  Registering this
as an instance makes the consequences of `e8_isKilling` available by `inferInstance`: with
`haveI := e8_isKilling` one gets `LieAlgebra.IsSemisimple ℂ (e₈ ℂ)`,
`LieAlgebra.HasTrivialRadical ℂ (e₈ ℂ)`, and the whole `LieAlgebra.IsKilling` API. -/
instance e8_moduleFinite : Module.Finite ℂ (LieAlgebra.e₈ ℂ) :=
  Module.finite_of_finrank_pos (by rw [e8_finrank]; norm_num)

/-- A nonzero element of a subspace stable under all the `ad (SerreH i)` has a nonzero component
in some integral weight space `e8W μ`. -/
theorem exists_e8W_inf_ne_bot {W' : Submodule ℂ L8}
    (hW' : ∀ i : Fin 8, ∀ x ∈ W', ⁅SerreH i, x⁆ ∈ W') {y : L8} (hy : y ∈ W') (hy0 : y ≠ 0) :
    ∃ μ : Fin 8 → ℤ, W' ⊓ e8W μ ≠ ⊥ := by
  classical
  have hx : y ∈ ⨆ μ : Fin 8 → ℤ, e8W μ := by rw [e8W_iSup_eq_top]; trivial
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hx
  obtain ⟨f, hf, hsum⟩ := mem_iSup_finset_iff.mp hs
  have hfW : ∀ m ∈ s, f m ∈ W (fun j => ((m j : ℤ) : ℂ)) := fun m hm => by
    rw [← e8W_eq_W]; exact hf m hm
  let π : L8 →ₗ[ℂ] L8 ⧸ W' := W'.mkQ
  let T : Fin 8 → Module.End ℂ (L8 ⧸ W') := fun i =>
    W'.mapQ W' (LieAlgebra.ad ℂ L8 (SerreH i)) (fun x hx => by
      show (LieAlgebra.ad ℂ L8 (SerreH i)) x ∈ W'
      rw [LieAlgebra.ad_apply]
      exact hW' i x hx)
  have hπapply : ∀ z : L8, π z = (Submodule.Quotient.mk z : L8 ⧸ W') := fun z =>
    Submodule.mkQ_apply W' z
  have hTapply : ∀ (i : Fin 8) (z : L8), T i (π z) = π ⁅SerreH i, z⁆ := by
    intro i z
    rw [hπapply]
    show (W'.mapQ W' (LieAlgebra.ad ℂ L8 (SerreH i)) _) (Submodule.Quotient.mk z) =
      (Submodule.Quotient.mk ⁅SerreH i, z⁆ : L8 ⧸ W')
    rw [Submodule.mapQ_apply]
    rfl
  have heig : ∀ (μ : Fin 8 → ℤ), μ ∈ s → ∀ i : Fin 8,
      T i (π (f μ)) = ((μ i : ℤ) : ℂ) • π (f μ) := by
    intro μ hμ i
    rw [hTapply, mem_W_iff.mp (hfW μ hμ) i, map_smul]
  let s' : Finset (Fin 8 → ℤ) := s.filter (fun μ => π (f μ) ≠ 0)
  have hsum_aux : ∑ μ ∈ s', (1 : ℂ) • π (f μ) = 0 := by
    have h1 : ∑ μ ∈ s', (1 : ℂ) • π (f μ) = ∑ μ ∈ s, (1 : ℂ) • π (f μ) := by
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro μ hμs hμnot
      rw [Finset.mem_filter] at hμnot
      have hz : π (f μ) = 0 := by
        by_contra hcon
        exact hμnot ⟨hμs, hcon⟩
      rw [hz, smul_zero]
    rw [h1]
    simp only [one_smul]
    rw [← map_sum, ← hsum, hπapply, Submodule.Quotient.mk_eq_zero]
    exact hy
  have hsum_univ : ∑ μ : {μ : Fin 8 → ℤ // μ ∈ s'}, (1 : ℂ) • π (f μ.1) = 0 := by
    rw [Finset.univ_eq_attach s', Finset.sum_attach s' (fun μ => (1 : ℂ) • π (f μ))]
    exact hsum_aux
  have hs'_empty : s' = ∅ := by
    by_contra hempty
    have hne : s'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨μ₀, hμ₀⟩ := hne
    have hkey := Commons.LinearAlgebra.Eigenvector.linearIndependent_of_separating_eigenvalues
      (K := ℂ) (M := L8 ⧸ W') (ι := {μ : Fin 8 → ℤ // μ ∈ s'}) (κ := Fin 8)
      T (fun μ => π (f μ.1)) (fun μ => (Finset.mem_filter.mp μ.2).2)
      (fun μ i => ((μ.1 i : ℤ) : ℂ))
      (fun μ i => heig μ.1 (Finset.mem_filter.mp μ.2).1 i)
      (fun μ ν hμν => by
        have h1 : μ.1 ≠ ν.1 := fun h => hμν (Subtype.ext h)
        obtain ⟨k, hk⟩ := Function.ne_iff.mp h1
        exact ⟨k, by exact_mod_cast hk⟩)
      (fun _ => 1) hsum_univ ⟨μ₀, hμ₀⟩
    norm_num at hkey
  have hzero : ∀ μ ∈ s, f μ ∈ W' := by
    intro μ hμs
    have : π (f μ) = 0 := by
      by_contra hcon
      have : μ ∈ s' := Finset.mem_filter.mpr ⟨hμs, hcon⟩
      rw [hs'_empty] at this
      exact Finset.notMem_empty μ this
    rw [hπapply, Submodule.Quotient.mk_eq_zero] at this
    exact this
  have hex : ∃ μ ∈ s, f μ ≠ 0 := by
    by_contra h
    push Not at h
    exact hy0 (by rw [hsum, Finset.sum_eq_zero h])
  obtain ⟨μ, hμs, hμne⟩ := hex
  exact ⟨μ, by
    rw [Submodule.ne_bot_iff]
    exact ⟨f μ, Submodule.mem_inf.mpr ⟨hzero μ hμs, hf μ hμs⟩, hμne⟩⟩

/-- The weight space of `0` is the span of the `H`-generators. -/
theorem e8W_zero_eq_span_SerreH :
    e8W (0 : Fin 8 → ℤ) = Submodule.span ℂ (Set.range SerreH) := by
  have hW : e8W (0 : Fin 8 → ℤ) = W (0 : Fin 8 → ℂ) := by
    rw [e8W_eq_W]
    congr 1
    funext i
    simp
  rw [hW]
  have h1 : Module.finrank ℂ ↥(W (0 : Fin 8 → ℂ)) = 8 := by
    unfold W
    exact e8_zero_weightSpace_finrank
  have : FiniteDimensional ℂ ↥(W (0 : Fin 8 → ℂ)) :=
    Module.finite_of_finrank_pos (by rw [h1]; norm_num)
  have hH_le : Submodule.span ℂ (Set.range SerreH) ≤ W 0 :=
    Submodule.span_le.mpr (by rintro y ⟨i, rfl⟩; exact SerreH_mem_W_zero i)
  exact (Submodule.eq_of_le_of_finrank_le hH_le (by
    rw [h1, finrank_span_eq_card e8_H_linearIndependent]; simp)).symm

noncomputable def reflAutList : List (Fin 8) → (L8 ≃ₗ⁅ℂ⁆ L8)
  | [] => LieEquiv.refl (R := ℂ)
  | i :: L => (reflAut i).trans (reflAutList L)

lemma reflAutList_maps_W (L : List (Fin 8)) (μ : Fin 8 → ℂ) :
    ∀ {x : L8}, x ∈ W μ → reflAutList L x ∈ W (L.foldl (fun v i => sMu i v) μ) := by
  induction L generalizing μ with
  | nil =>
    intro x hx
    show x ∈ W μ
    exact hx
  | cons i L ih =>
    intro x hx
    rw [List.foldl_cons]
    show reflAutList L (reflAut i x) ∈ W (L.foldl (fun v i => sMu i v) (sMu i μ))
    exact ih (sMu i μ) (maps_W i (reflAut i) (reflAut_H i) hx)

lemma sMu_cast (ν : Fin 8 → ℤ) (i : Fin 8) :
    sMu i (fun j => ((ν j : ℤ) : ℂ))
      = fun j => (((fun j => ν j - ν i * CartanMatrix.E₈ i j) j : ℤ) : ℂ) := by
  funext j
  simp only [sMu]
  push_cast
  ring

lemma foldl_sMu_cast (L : List (Fin 8)) (ν : Fin 8 → ℤ) :
    L.foldl (fun v i => sMu i v) (fun j => ((ν j : ℤ) : ℂ))
      = fun j => ((L.foldl (fun v i => fun j => v j - v i * CartanMatrix.E₈ i j) ν) j : ℂ) := by
  induction L generalizing ν with
  | nil => rfl
  | cons i L ih =>
    rw [List.foldl_cons, List.foldl_cons, sMu_cast]
    exact ih (fun j => ν j - ν i * CartanMatrix.E₈ i j)

lemma reflAutList_e8W (L : List (Fin 8)) (μ : Fin 8 → ℤ) :
    ∀ {x : L8}, x ∈ e8W μ →
      reflAutList L x ∈ e8W (L.foldl (fun v i => fun j => v j - v i * CartanMatrix.E₈ i j) μ) := by
  intro x hx
  rw [e8W_eq_W] at hx ⊢
  rw [← foldl_sMu_cast]
  exact reflAutList_maps_W L _ hx

lemma W_alpha_eq_span (k : Fin 8) : W (alpha k) = ℂ ∙ SerreE k := by
  have hfin : Module.finrank ℂ ↥(W (alpha k)) = 1 := by
    unfold W alpha SerreH
    exact e8_simple_root_weightSpace_finrank_compat k
  have hle : (ℂ ∙ SerreE k : Submodule ℂ L8) ≤ W (alpha k) :=
    Submodule.span_le.mpr (by rintro y rfl; exact SerreE_mem_W k)
  have : FiniteDimensional ℂ ↥(W (alpha k)) := Module.finite_of_finrank_pos (by rw [hfin]; norm_num)
  exact (Submodule.eq_of_le_of_finrank_le hle (by
    rw [hfin, finrank_span_singleton (show SerreE k ≠ 0 from e8_serreE_ne_zero k)])).symm

/-- **The Killing form of the Serre-constructed `e₈` is non-degenerate.**

This is the gateway to the whole root-space / representation theory of `e₈` in Mathlib: with it,
`LieAlgebra.IsKilling.*` (in `Mathlib.Algebra.Lie.Weights.Killing`,
`Mathlib.Algebra.Lie.Weights.RootSystem`) supplies Cartan subalgebras, root spaces,
one-dimensionality of root spaces, `IsSl2Triple`s for every root and the Weyl group action.
It also gives `LieAlgebra.IsSemisimple ℂ (LieAlgebra.e₈ ℂ)` and `HasTrivialRadical ℂ (LieAlgebra.e₈ ℂ)`.

Suggested route (all the ingredients are already in the shared commons, under
`Submission/Commons/Algebra/Lie/SerreConstruction/`):

1. The weight space decomposition `e8_weightSpace_iSup_eq_top` gives
   `e₈ = 𝔥 ⊕ ⨁_{α ∈ Φ} g_α` with `𝔥 = e8W 0` of dimension `8`
   (`e8_zero_weightSpace_finrank`) and with `g_α` one-dimensional for every nonzero weight
   (`e8_root_weightSpace_finrank_eq_one`), the `SerreH i` forming a linearly independent family
   (`e8_H_linearIndependent`).

2. Every nonzero weight of the adjoint representation is a root: take a weight `μ ≠ 0`, replace it
   by `s_i μ` (`(s_iμ)_j = μ_j - μ_i A_{ij}`) whenever `μ i < 0` — by
   `e8_weightSpace_ascent` (iterated, since each step raises the `i`-th coordinate by `2`) this
   remains a weight; the process terminates with a dominant weight, which is `θ` by
   `e8_dominant_weight_eq_zero_or_theta`.  Use `qform_reflect` (`Algebra/Lie/e8_finrank.lean`) to
   see that the squared length `μᵀA⁻¹μ` is preserved, so that `μ` is a root
   (`exists_finset_e8_roots` describes the 240 roots).

3. Consequently `killingForm ℂ (e₈ ℂ) (SerreH i) (SerreH j) = ∑_{α ∈ Φ} α_i α_j`
   (`α = (α_i)_i` runs over the 240 roots in `ω`-coordinates) and this equals `60 * E8 i j`,
   which is invertible; hence the restriction of the Killing form to `𝔥` is non-degenerate.

4. For each root `α`, `[g_α, g_{-α}] ≠ 0`: reduce to a simple root by conjugating with the
   reflection automorphism `reflAut i : L8 ≃ₗ⁅ℂ⁆ L8` of
   `Submission/Commons/Algebra/Lie/SerreConstruction/e8_weightSpace_reflect_finrank.lean`
   (`reflAut_H`, `maps_W`), and use `⁅SerreE i, SerreF i⁆ = SerreH i ≠ 0`.

5. Now `killingForm` is non-degenerate: it is block-diagonal with respect to the decomposition in
   (1) (`killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero`, or directly from the weight
   decomposition), the `𝔥`-block is non-degenerate by (3), and the `g_α ⊕ g_{-α}`-block is
   non-degenerate by (4) together with (3): if `κ (g_α) (g_{-α}) = 0` then
   `[g_α, g_{-α}] ⊆ 𝔥` is `κ`-orthogonal to `𝔥`, hence zero. -/
theorem e8_isKilling : LieAlgebra.IsKilling ℂ (LieAlgebra.e₈ ℂ) := by
  -- Route: Cartan's criterion `LieAlgebra.HasTrivialRadical.instIsKilling` reduces the goal to
  -- triviality of the radical, i.e. (by `hasTrivialRadical_iff_no_abelian_ideals`) to the
  -- vanishing of every abelian ideal `I`.  Let `I ≠ 0` be an abelian ideal.  Being stable under
  -- all the `ad (SerreH i)`, it contains a nonzero weight vector `z` (`exists_e8W_inf_ne_bot`);
  -- if the weight is `0` then `z ∈ 𝔥 = span{Hᵢ} = e8W 0` yields coefficients `c` with
  -- `z = ∑ cᵢ Hᵢ`; linear independence of the `SerreH i` gives `c ≠ 0`, and invertibility of the
  -- Cartan matrix gives `k` with `∑ i, cᵢ A_{ik} ≠ 0`, whence `SerreE k ∈ I`.  If the weight is
  -- a root then `E8_norm_two_conj_simple` reflects it to a simple root `α_k` by a composition
  -- `reflAutList L` of the reflection automorphisms, giving `SerreE k` in the conjugate ideal,
  -- i.e. `(reflAutList L).symm (SerreE k) ∈ I`.  In both cases `H_k = [E_k, F_k] ∈ I` as well,
  -- and abelianness of `I` forces `[E_k, H_k] = -2 E_k = 0`, a contradiction.
  have hrad : LieAlgebra.HasTrivialRadical ℂ L8 := by
    rw [LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals]
    intro I hI
    refine le_bot_iff.mp ?_
    intro y hy
    by_contra hy0
    have habel : ∀ a ∈ (I : Submodule ℂ L8), ∀ b ∈ I, ⁅a, b⁆ = 0 := by
      intro a ha b hb
      have h := hI.trivial (⟨a, ha⟩ : ↥I) (⟨b, hb⟩ : ↥I)
      have h2 : ((⁅(⟨a, ha⟩ : ↥I), (⟨b, hb⟩ : ↥I)⁆ : ↥I) : L8) = ⁅a, b⁆ :=
        LieSubalgebra.coe_bracket (I : LieSubalgebra ℂ L8) ⟨a, ha⟩ ⟨b, hb⟩
      rw [← h2, h, Submodule.coe_zero]
    have hHstab : ∀ i : Fin 8, ∀ x ∈ (I : Submodule ℂ L8), ⁅SerreH i, x⁆ ∈ (I : Submodule ℂ L8) :=
      fun i x hx => I.lie_mem (x := SerreH i) hx
    obtain ⟨μ, hμ⟩ := exists_e8W_inf_ne_bot (W' := (I : Submodule ℂ L8)) hHstab hy hy0
    obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).mp hμ
    have hzI : z ∈ (I : Submodule ℂ L8) := (Submodule.mem_inf.mp hz).1
    have hzW : z ∈ e8W μ := (Submodule.mem_inf.mp hz).2
    rcases eq_or_ne μ 0 with rfl | hμne
    · -- μ = 0
      rw [e8W_zero_eq_span_SerreH] at hzW
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hzW
      have hcne : c ≠ 0 := by
        intro h0
        apply hz0
        rw [← hc, h0]
        simp
      have hker : ∃ k : Fin 8, (∑ i, c i * ((CartanMatrix.E₈ i k : ℤ) : ℂ)) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        refine hcne ?_
        have h1 : Matrix.mulVec (CartanMatrix.E₈.map (Int.castRingHom ℂ)) c = 0 := by
          funext k
          have hsym : ∀ j : Fin 8,
              ((CartanMatrix.E₈.map (Int.castRingHom ℂ)) k j) = ((CartanMatrix.E₈ j k : ℤ) : ℂ) := by
            intro j
            rw [Matrix.map_apply,
              show CartanMatrix.E₈ k j = CartanMatrix.E₈ j k from E8_symm k j]
            simp
          rw [Matrix.mulVec, dotProduct, Pi.zero_apply]
          rw [Finset.sum_congr rfl (fun j _ => by rw [hsym j, mul_comm])]
          exact hcon k
        have h3 : (Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv.map (Int.castRingHom ℂ))
            * (CartanMatrix.E₈.map (Int.castRingHom ℂ)) = 1 := by
          rw [← Matrix.map_mul, Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv_mul_E8]
          ext i j
          simp [Matrix.one_apply]
        calc c = Matrix.mulVec (1 : Matrix (Fin 8) (Fin 8) ℂ) c := by rw [Matrix.one_mulVec]
          _ = Matrix.mulVec ((Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv.map
                (Int.castRingHom ℂ)) * (CartanMatrix.E₈.map (Int.castRingHom ℂ))) c := by rw [h3]
          _ = Matrix.mulVec (Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv.map
                (Int.castRingHom ℂ)) (Matrix.mulVec (CartanMatrix.E₈.map (Int.castRingHom ℂ)) c) := by
                rw [Matrix.mulVec_mulVec]
          _ = 0 := by rw [h1, Matrix.mulVec_zero]
      obtain ⟨k, hk⟩ := hker
      have hbk : ⁅z, SerreE k⁆ = (∑ i, c i * ((CartanMatrix.E₈ i k : ℤ) : ℂ)) • SerreE k := by
        rw [← hc, sum_lie, Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_lie, serreLie_H_E, zsmul_int_eq, smul_smul]
      have hbk' : ⁅SerreE k, z⁆ = (-(∑ i, c i * ((CartanMatrix.E₈ i k : ℤ) : ℂ))) • SerreE k := by
        rw [← lie_skew (SerreE k) z, hbk, neg_smul]
      have hmem : ⁅SerreE k, z⁆ ∈ (I : Submodule ℂ L8) := I.lie_mem (x := SerreE k) hzI
      have hEk : SerreE k ∈ (I : Submodule ℂ L8) := by
        have h2 : SerreE k
            = (-(∑ i, c i * ((CartanMatrix.E₈ i k : ℤ) : ℂ)))⁻¹ • ⁅SerreE k, z⁆ := by
          rw [hbk', smul_smul, inv_mul_cancel₀ (by simpa using hk), one_smul]
        rw [h2]
        exact I.smul_mem _ hmem
      have hHk : SerreH k ∈ (I : Submodule ℂ L8) := by
        have h3 : ⁅SerreE k, SerreF k⁆ = SerreH k := by rw [serreLie_E_F k k, if_pos rfl]
        rw [← h3, ← lie_skew (SerreE k) (SerreF k)]
        exact I.neg_mem (I.lie_mem (x := SerreF k) hEk)
      have hcontra : ⁅SerreE k, SerreH k⁆ = 0 := habel _ hEk _ hHk
      have hEH : ⁅SerreE k, SerreH k⁆ = (-2 : ℂ) • SerreE k := by
        rw [← lie_skew (SerreE k) (SerreH k), serreLie_H_E, E8_diag]
        module
      rw [hEH] at hcontra
      exact e8_serreE_ne_zero k ((smul_eq_zero.mp hcontra).resolve_left (by norm_num))
    · -- μ ≠ 0 : a root
      have hroot : e8Nrm μ = 2 := by
        by_contra h2
        rw [e8W_eq_bot_of_not_root μ hμne h2] at hzW
        exact hz0 ((Submodule.mem_bot ℂ).mp hzW)
      obtain ⟨L, k, hL⟩ := Commons.LinearAlgebra.Matrix.Cartan.E8_norm_two_conj_simple μ hroot
      have hmap : reflAutList L z ∈ e8W (fun i => CartanMatrix.E₈ k i) := by
        have h := reflAutList_e8W L μ hzW
        rwa [hL] at h
      have hmapW : reflAutList L z ∈ W (alpha k) := by
        change reflAutList L z ∈ W (fun i => ((CartanMatrix.E₈ k i : ℤ) : ℂ))
        rw [← e8W_eq_W (fun i => CartanMatrix.E₈ k i)]
        exact hmap
      have hz'0 : reflAutList L z ≠ 0 := by
        intro h
        apply hz0
        have hh := congrArg (reflAutList L).symm h
        simpa using hh
      rw [W_alpha_eq_span] at hmapW
      obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hmapW
      have hcc0 : cc ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hcc
        exact hz'0 hcc.symm
      have hE : (reflAutList L).symm (SerreE k) ∈ (I : Submodule ℂ L8) := by
        have h2 : cc • (reflAutList L).symm (SerreE k) = z := by
          have hh := congrArg (reflAutList L).symm hcc
          simpa using hh
        have h1 : (reflAutList L).symm (SerreE k) = cc⁻¹ • z := by
          rw [← h2, smul_smul, inv_mul_cancel₀ hcc0, one_smul]
        rw [h1]
        exact I.smul_mem _ hzI
      have hH : (reflAutList L).symm (SerreH k) ∈ (I : Submodule ℂ L8) := by
        rw [show (reflAutList L).symm (SerreH k)
            = ⁅(reflAutList L).symm (SerreE k), (reflAutList L).symm (SerreF k)⁆ from by
          rw [← (reflAutList L).symm.map_lie, serreLie_E_F k k, if_pos rfl],
          ← lie_skew ((reflAutList L).symm (SerreE k)) ((reflAutList L).symm (SerreF k))]
        exact I.neg_mem (I.lie_mem (x := (reflAutList L).symm (SerreF k)) hE)
      have hcontra : ⁅(reflAutList L).symm (SerreE k), (reflAutList L).symm (SerreH k)⁆ = 0 :=
        habel _ hE _ hH
      have hEH : ⁅(reflAutList L).symm (SerreE k), (reflAutList L).symm (SerreH k)⁆
          = (-2 : ℂ) • (reflAutList L).symm (SerreE k) := by
        have h0 : ⁅SerreE k, SerreH k⁆ = (-2 : ℂ) • SerreE k := by
          rw [← lie_skew (SerreE k) (SerreH k), serreLie_H_E, E8_diag]
          module
        rw [← (reflAutList L).symm.map_lie, h0, map_smul]
      rw [hEH] at hcontra
      have hne : (reflAutList L).symm (SerreE k) ≠ 0 := by
        intro h
        have hh : SerreE k = 0 := by
          have h2 := congrArg (reflAutList L) h
          simpa using h2
        exact e8_serreE_ne_zero k hh
      exact hne ((smul_eq_zero.mp hcontra).resolve_left (by norm_num))
  exact LieAlgebra.HasTrivialRadical.instIsKilling ℂ L8

end
end Commons.Algebra.Lie.SerreConstruction


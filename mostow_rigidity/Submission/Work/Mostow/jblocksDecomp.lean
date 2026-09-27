import Mathlib

namespace Work.Mostow

open scoped RealInnerProductSpace

/-- Reindexing an orthonormal family by an equivalence. -/
private lemma orthonormal_comp_equiv {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι ι' : Type*} (e : ι' ≃ ι) {f : ι → E}
    (hf : Orthonormal ℝ f) : Orthonormal ℝ (f ∘ e) :=
  ⟨fun i => hf.1 (e i), fun _ _ hij => hf.2 fun h => hij (e.injective h)⟩

/-- Orthonormality of a family indexed by a sum of two families that are mutually orthogonal. -/
private lemma orthonormal_sum_elim {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι κ : Type*} {v : ι → E} {w : κ → E}
    (hv : Orthonormal ℝ v) (hw : Orthonormal ℝ w)
    (hcross : ∀ i j, inner ℝ (v i) (w j) = 0) : Orthonormal ℝ (Sum.elim v w) := by
  refine ⟨?_, ?_⟩
  · rintro (i | j)
    · exact hv.1 i
    · exact hw.1 j
  · intro a b hab
    rcases a with i | i <;> rcases b with j | j
    · exact hv.2 fun h => hab (by rw [h])
    · exact hcross i j
    · rw [real_inner_comm]; exact hcross j i
    · exact hw.2 fun h => hab (by rw [h])

/-- A norm-preserving linear map on a submodule preserves the inner product there. -/
private lemma inner_map_map_of_norm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {P : Submodule ℝ V} {J : V →ₗ[ℝ] V} (hJi : ∀ x ∈ P, ‖J x‖ = ‖x‖) :
    ∀ a ∈ P, ∀ b ∈ P, inner ℝ (J a) (J b) = inner ℝ a b := by
  intro a ha b hb
  have hJab : ‖J a + J b‖ = ‖a + b‖ := by
    rw [← map_add J a b, hJi (a + b) (P.add_mem ha hb)]
  have e1 := norm_add_sq_real (J a) (J b)
  have e2 := norm_add_sq_real a b
  rw [hJab, hJi a ha, hJi b hb] at e1
  linarith [e1, e2]

/-- Auxiliary form of `jblocksDecomp`, by strong induction on `finrank ℝ P`. -/
private theorem exists_blockDecomp_aux {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] :
    ∀ d : ℕ, ∀ (P : Submodule ℝ V) (J : V →ₗ[ℝ] V),
      Module.finrank ℝ P = d →
      (∀ x ∈ P, J (J x) = -x) → (∀ x ∈ P, ‖J x‖ = ‖x‖) → (∀ x ∈ P, J x ∈ P) →
      ∃ (κ : Type) (_ : Fintype κ) (u : κ → V),
        (∀ i, u i ∈ P) ∧
        Orthonormal ℝ (fun j : κ × Fin 2 => if j.2 = (0 : Fin 2) then u j.1 else J (u j.1)) ∧
        Submodule.span ℝ (Set.range (fun j : κ × Fin 2 =>
          if j.2 = (0 : Fin 2) then u j.1 else J (u j.1))) = P := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro P J hfin hJ2 hJi hJmem
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · -- base case: `P` is trivial
      have hP0 : Module.finrank ℝ P = 0 := by omega
      have hPbot : P = ⊥ := (Submodule.finrank_eq_zero).mp hP0
      refine ⟨Fin 0, inferInstance, fun i : Fin 0 => Fin.elim0 i, ?_, ?_, ?_⟩
      · intro i; exact Fin.elim0 i
      · refine ⟨fun i => Fin.elim0 i.1, fun a b _ => Fin.elim0 a.1⟩
      · rw [hPbot]
        rw [show (Set.range (fun j : Fin 0 × Fin 2 =>
            if j.2 = (0 : Fin 2) then (Fin.elim0 j.1 : V) else J (Fin.elim0 j.1))) = ∅ from ?_,
          Submodule.span_empty]
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨j, -⟩
        exact Fin.elim0 j.1
    · -- inductive step
      have hposP : 0 < Module.finrank ℝ P := by omega
      haveI : Nontrivial ↥P := (Module.finrank_pos_iff).mp hposP
      obtain ⟨x, hxne⟩ := exists_ne (0 : ↥P)
      have hxVne : (x : V) ≠ 0 := by
        intro h; exact hxne (Subtype.ext (by simpa using h))
      have hnormx : ‖(x : V)‖ ≠ 0 := norm_ne_zero_iff.mpr hxVne
      set u : V := (‖(x : V)‖)⁻¹ • (x : V) with hu
      have hnormu : ‖u‖ = 1 := by
        rw [hu, norm_smul, norm_inv, norm_norm]
        exact inv_mul_cancel₀ hnormx
      have huP : u ∈ P := by rw [hu]; exact P.smul_mem _ x.2
      have hJnormu : ‖J u‖ = 1 := by rw [hJi u huP, hnormu]
      have hinner : inner ℝ u (J u) = 0 := by
        have hJuu : J (J u) = -u := hJ2 u huP
        have hh := inner_map_map_of_norm hJi u huP (J u) (hJmem u huP)
        rw [hJuu, inner_neg_right, real_inner_comm u (J u)] at hh
        linarith
      set W : Submodule ℝ V := Submodule.span ℝ ({u, J u} : Set V) with hW
      have hWle : W ≤ P := by
        rw [hW]
        refine Submodule.span_le.mpr ?_
        rintro v (hv : v ∈ ({u, J u} : Set V))
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl
        · exact huP
        · exact hJmem u huP
      have hWinv : ∀ w ∈ W, J w ∈ W := by
        have hle : Submodule.span ℝ ({u, J u} : Set V) ≤ Submodule.comap J W := by
          refine Submodule.span_le.mpr ?_
          rintro v (hv : v ∈ ({u, J u} : Set V))
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
          rcases hv with rfl | rfl
          · exact Submodule.mem_comap.mpr
              (by rw [hW]; exact Submodule.subset_span (by simp))
          · exact Submodule.mem_comap.mpr
              (by rw [hJ2 u huP, hW]
                  exact Submodule.neg_mem _ (Submodule.subset_span (by simp)))
        intro w hw
        exact Submodule.mem_comap.mp (hle (by rw [← hW]; exact hw))
      set Q : Submodule ℝ V := Wᗮ ⊓ P with hQ
      have hsupQ : W ⊔ Q = P := by
        rw [hQ]
        exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hWle
      have hfinPQ : Module.finrank ℝ P = Module.finrank ℝ W + Module.finrank ℝ Q := by
        have h1 := Submodule.finrank_sup_add_finrank_inf_eq W Q
        rw [hsupQ] at h1
        have h2 : W ⊓ Q = ⊥ := by
          rw [hQ, ← inf_assoc, (Submodule.isCompl_orthogonal W).inf_eq_bot, bot_inf_eq]
        have hbot : Module.finrank ℝ (⊥ : Submodule ℝ V) = 0 :=
          (Submodule.finrank_eq_zero).mpr rfl
        rw [h2, hbot, add_zero] at h1
        exact h1
      have huW : u ∈ W := by rw [hW]; exact Submodule.subset_span (by simp)
      have hune : u ≠ 0 := by
        intro h; rw [h, norm_zero] at hnormu; exact one_ne_zero hnormu.symm
      have hWne : W ≠ ⊥ := by
        intro h; exact hune (by rw [h] at huW; simpa using huW)
      have hWpos : 0 < Module.finrank ℝ W := by
        have hz : Module.finrank ℝ W ≠ 0 := fun hz => hWne ((Submodule.finrank_eq_zero).mp hz)
        omega
      have hQlt : Module.finrank ℝ Q < d := by omega
      have hJ2Q : ∀ y ∈ Q, J (J y) = -y := fun y hy => hJ2 y hy.2
      have hJiQ : ∀ y ∈ Q, ‖J y‖ = ‖y‖ := fun y hy => hJi y hy.2
      have hJmemQ : ∀ y ∈ Q, J y ∈ Q := by
        intro y hy
        refine ⟨?_, hJmem y hy.2⟩
        change ∀ w ∈ W, inner ℝ w (J y) = 0
        intro w hw
        have hwP : w ∈ P := hWle hw
        have hJwW : J w ∈ W := hWinv w hw
        have hJwP : J w ∈ P := hWle hJwW
        have h1 : J (J w) = -w := hJ2 w hwP
        calc inner ℝ w (J y)
            = inner ℝ (-(J (J w))) (J y) := by rw [h1, neg_neg]
          _ = - inner ℝ (J (J w)) (J y) := by rw [inner_neg_left]
          _ = - inner ℝ (J w) y := by
                rw [inner_map_map_of_norm hJi (J w) hJwP y hy.2]
          _ = 0 := by
                rw [(Submodule.mem_orthogonal W y).mp hy.1 (J w) hJwW, neg_zero]
      obtain ⟨κ', hκ'fin, u', hu'mem, hu'orth, hu'span⟩ :=
        ih (Module.finrank ℝ Q) hQlt Q J rfl hJ2Q hJiQ hJmemQ
      letI := hκ'fin
      set U : Sum Unit κ' → V := Sum.elim (fun _ => u) u' with hU
      have hb0 : Orthonormal ℝ (fun i : Unit × Fin 2 =>
          if i.2 = (0 : Fin 2) then u else J u) := by
        rw [orthonormal_iff_ite]
        rintro ⟨a, b⟩ ⟨a', b'⟩
        fin_cases b <;> fin_cases b' <;>
          simp [hnormu, hJnormu, hinner, real_inner_self_eq_norm_sq, real_inner_comm]
      have hb' : Orthonormal ℝ (fun j : κ' × Fin 2 =>
          if j.2 = (0 : Fin 2) then u' j.1 else J (u' j.1)) := hu'orth
      have hcross : ∀ (i : Unit × Fin 2) (j : κ' × Fin 2),
          inner ℝ (if i.2 = (0 : Fin 2) then u else J u)
            (if j.2 = (0 : Fin 2) then u' j.1 else J (u' j.1)) = 0 := by
        intro i j
        have hiW : (if i.2 = (0 : Fin 2) then u else J u) ∈ W := by
          rcases i with ⟨a, c⟩
          by_cases hc : c = (0 : Fin 2)
          · rw [if_pos hc]; exact huW
          · rw [if_neg hc]; exact hWinv u huW
        have hjW : (if j.2 = (0 : Fin 2) then u' j.1 else J (u' j.1)) ∈ Wᗮ := by
          rcases j with ⟨k, c⟩
          by_cases hc : c = (0 : Fin 2)
          · rw [if_pos hc]; exact (hu'mem k).1
          · rw [if_neg hc]; exact (hJmemQ (u' k) (hu'mem k)).1
        exact (Submodule.mem_orthogonal W _).mp hjW _ hiW
      have hmix : Orthonormal ℝ (Sum.elim
          (fun i : Unit × Fin 2 => if i.2 = (0 : Fin 2) then u else J u)
          (fun j : κ' × Fin 2 => if j.2 = (0 : Fin 2) then u' j.1 else J (u' j.1))) :=
        orthonormal_sum_elim hb0 hb' hcross
      have heq : (fun j : (Sum Unit κ') × Fin 2 =>
            if j.2 = (0 : Fin 2) then U j.1 else J (U j.1))
          = (Sum.elim
              (fun i : Unit × Fin 2 => if i.2 = (0 : Fin 2) then u else J u)
              (fun j : κ' × Fin 2 => if j.2 = (0 : Fin 2) then u' j.1 else J (u' j.1)))
            ∘ (Equiv.sumProdDistrib Unit κ' (Fin 2)) := by
        funext j
        rcases j with ⟨(i | i), c⟩
        · simp [U, Equiv.sumProdDistrib]
        · simp [U, Equiv.sumProdDistrib]
      have hrange0 : Set.range (fun i : Unit × Fin 2 =>
          if i.2 = (0 : Fin 2) then u else J u) = ({u, J u} : Set V) := by
        ext v
        constructor
        · rintro ⟨⟨a, c⟩, rfl⟩
          by_cases hc : c = (0 : Fin 2)
          · simp [hc]
          · simp [hc]
        · intro hv
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
          rcases hv with rfl | rfl
          · exact ⟨((), 0), by simp⟩
          · exact ⟨((), 1), by simp⟩
      have hspan0 : Submodule.span ℝ (Set.range (fun i : Unit × Fin 2 =>
          if i.2 = (0 : Fin 2) then u else J u)) = W := by
        rw [hrange0, hW]
      refine ⟨Sum Unit κ', inferInstance, U, ?_, ?_, ?_⟩
      · intro i
        rcases i with i | i
        · exact huP
        · exact (hu'mem i).2
      · rw [heq]
        exact orthonormal_comp_equiv _ hmix
      · rw [heq]
        rw [show Set.range ((Sum.elim
              (fun i : Unit × Fin 2 => if i.2 = (0 : Fin 2) then u else J u)
              (fun j : κ' × Fin 2 => if j.2 = (0 : Fin 2) then u' j.1 else J (u' j.1)))
              ∘ (Equiv.sumProdDistrib Unit κ' (Fin 2)))
            = Set.range (Sum.elim
              (fun i : Unit × Fin 2 => if i.2 = (0 : Fin 2) then u else J u)
              (fun j : κ' × Fin 2 => if j.2 = (0 : Fin 2) then u' j.1 else J (u' j.1)))
            from ?_]
        · rw [Set.Sum.elim_range, Submodule.span_union, hspan0, hu'span, hsupQ]
        · rw [Set.range_comp, (Equiv.surjective (Equiv.sumProdDistrib Unit κ' (Fin 2))).range_eq,
            Set.image_univ]

/-- If `P` is a submodule of a finite-dimensional real inner product space `V` carrying an
orthogonal complex structure `J` (i.e. `J ∘ J = -id` and `J` is norm-preserving on `P`, and `J`
maps `P` into itself), then `P` is spanned by an orthonormal family of `J`-invariant blocks
`(u i, J (u i))`. -/
theorem jblocksDecomp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (P : Submodule ℝ V) (J : V →ₗ[ℝ] V)
    (hJ2 : ∀ x ∈ P, J (J x) = -x) (hJi : ∀ x ∈ P, ‖J x‖ = ‖x‖)
    (hJmem : ∀ x ∈ P, J x ∈ P) :
    ∃ (κ : Type) (_ : Fintype κ) (u : κ → V),
      (∀ i, u i ∈ P) ∧
      Orthonormal ℝ (fun j : κ × Fin 2 => if j.2 = (0 : Fin 2) then u j.1 else J (u j.1)) ∧
      Submodule.span ℝ (Set.range (fun j : κ × Fin 2 =>
        if j.2 = (0 : Fin 2) then u j.1 else J (u j.1))) = P :=
  exists_blockDecomp_aux (Module.finrank ℝ P) P J rfl hJ2 hJi hJmem

end Work.Mostow

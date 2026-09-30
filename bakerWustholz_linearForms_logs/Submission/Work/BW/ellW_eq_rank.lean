import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.wuestholzDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Linear-algebra core of `ellW_eq_rank`.  For a finite family `w` of vectors and a finite
family `L` of linear forms, the codimension of `span w ∩ ⋂ᵢ ker Lᵢ` inside `span w` is the
rank of the matrix `(Lᵢ (w k))`. -/
theorem finrank_span_sub_infi_ker_eq_rank
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (w : ι → V) (L : ι' → V →ₗ[K] K) :
    Module.finrank K (Submodule.span K (Set.range w)) -
        Module.finrank K ((Submodule.span K (Set.range w) ⊓ ⨅ i : ι', LinearMap.ker (L i) :
          Submodule K V)) =
      (Matrix.of (fun (i : ι') (k : ι) => L i (w k))).rank := by
  classical
  set W : Submodule K V := Submodule.span K (Set.range w) with hW
  have hker_pi : LinearMap.ker (LinearMap.pi L) = ⨅ i : ι', LinearMap.ker (L i) :=
    LinearMap.ker_pi L
  have hker_g : LinearMap.ker (LinearMap.pi L ∘ₛₗ W.subtype) =
      Submodule.comap W.subtype (LinearMap.ker (LinearMap.pi L)) := LinearMap.ker_comp _ _
  have hmap : Submodule.map W.subtype (LinearMap.ker (LinearMap.pi L ∘ₛₗ W.subtype)) =
      W ⊓ ⨅ i : ι', LinearMap.ker (L i) := by
    rw [hker_g, Submodule.map_comap_subtype, hker_pi]
  have hfin : Module.finrank K (LinearMap.ker (LinearMap.pi L ∘ₛₗ W.subtype)) =
      Module.finrank K ((W ⊓ ⨅ i : ι', LinearMap.ker (L i) : Submodule K V)) := by
    rw [← hmap, Submodule.finrank_map_subtype_eq]
  have hran := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi L ∘ₛₗ W.subtype)
  have hsub : Module.finrank K W -
      Module.finrank K ((W ⊓ ⨅ i : ι', LinearMap.ker (L i) : Submodule K V)) =
      Module.finrank K (LinearMap.range (LinearMap.pi L ∘ₛₗ W.subtype)) := by
    rw [← hfin]
    omega
  have hrange : LinearMap.range (LinearMap.pi L ∘ₛₗ W.subtype) =
      Submodule.span K (Set.range (Matrix.of (fun (i : ι') (k : ι) => L i (w k))).col) := by
    have himg : (LinearMap.pi L) '' Set.range w =
        Set.range (Matrix.of (fun (i : ι') (k : ι) => L i (w k))).col := by
      ext z
      constructor
      · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, rfl⟩
      · rintro ⟨k, rfl⟩
        exact ⟨w k, ⟨k, rfl⟩, rfl⟩
    rw [LinearMap.range_comp, Submodule.range_subtype, hW, Submodule.map_span, himg]
  rw [hsub, hrange]
  exact (Matrix.rank_eq_finrank_span_cols _).symm

/-- Value of `chiFun` on the `j`-th row of `M` (the `castSucc` indices). -/
lemma chiFun_castSucc {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (v : Fin (N + 1) → ℂ) (i : Fin ρ) :
    chiFun M v i.castSucc = ∑ k : Fin N, (M i k : ℂ) * v k.succ := by
  have hi : ((i.castSucc : Fin (ρ + 1)) : ℕ) < ρ := by rw [Fin.val_castSucc]; exact i.isLt
  have hidx : (⟨(i.castSucc : Fin (ρ + 1)), hi⟩ : Fin ρ) = i := Fin.ext rfl
  simp only [chiFun]
  rw [dite_eq_left hi, hidx]

/-- Value of `chiFun` on the last index (the `G_a`-coordinate). -/
lemma chiFun_last {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (v : Fin (N + 1) → ℂ) :
    chiFun M v (Fin.last ρ) = v 0 := by
  have h : ¬ (((Fin.last ρ : Fin (ρ + 1)) : ℕ) < ρ) := by simp
  simp only [chiFun]
  rw [dite_eq_right h]

/-- `ℓ = dim W − dim (W ∩ Lie G')` is the rank of the matrix of the linear forms cutting out
`Lie G'`: the `ρ` character rows when `ε = true`, together with the `G_a`-coordinate when
`ε = false`. -/
theorem ellW_eq_rank {N q ρ : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (M : Fin ρ → Fin N → ℤ) :
    (ellW w true M =
        (Matrix.of (fun (j : Fin ρ) (k : Fin q) => ∑ i : Fin N, (M j i : ℂ) * w k i.succ)).rank) ∧
    (ellW w false M =
        (Matrix.of (fun (j : Fin (ρ + 1)) (k : Fin q) => chiFun M (w k) j)).rank) := by
  let L : Fin ρ → (Fin (N + 1) → ℂ) →ₗ[ℂ] ℂ := fun j =>
    ∑ i : Fin N, (M j i : ℂ) • LinearMap.proj (R := ℂ) (φ := fun _ : Fin (N + 1) => ℂ) i.succ
  let L' : Fin (ρ + 1) → (Fin (N + 1) → ℂ) →ₗ[ℂ] ℂ :=
    Fin.lastCases (LinearMap.proj (R := ℂ) (φ := fun _ : Fin (N + 1) => ℂ) 0) (fun i => L i)
  have hLval : ∀ (j : Fin ρ) (k : Fin q),
      L j (w k) = ∑ i : Fin N, (M j i : ℂ) * w k i.succ := by
    intro j k
    simp only [L, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  have hcast : ∀ i : Fin ρ, L' i.castSucc = L i := by
    intro i
    simp only [L', Fin.lastCases_castSucc]
  have hlast : L' (Fin.last ρ) =
      LinearMap.proj (R := ℂ) (φ := fun _ : Fin (N + 1) => ℂ) 0 := by
    simp only [L', Fin.lastCases_last]
  have hL'val : ∀ (j : Fin (ρ + 1)) (k : Fin q), L' j (w k) = chiFun M (w k) j := by
    intro j k
    refine Fin.lastCases ?_ ?_ j
    · rw [hlast, chiFun_last]
      simp only [LinearMap.proj_apply]
    · intro i
      rw [hcast i, hLval i k, chiFun_castSucc]
  constructor
  · have hlie : lieSub N ρ true M = ⨅ j : Fin ρ, LinearMap.ker (L j) := by
      simp only [lieSub, ite_true, top_inf_eq, L]
    rw [ellW, hlie, finrank_span_sub_infi_ker_eq_rank w L]
    congr 1
    funext j k
    exact hLval j k
  · have hsplit : (⨅ j : Fin (ρ + 1), LinearMap.ker (L' j)) =
        (⨅ j : Fin ρ, LinearMap.ker (L' j.castSucc)) ⊓ LinearMap.ker (L' (Fin.last ρ)) := by
      ext v
      simp only [Submodule.mem_iInf, Submodule.mem_inf, Fin.forall_fin_succ']
    have hInf : (⨅ j : Fin ρ, LinearMap.ker (L' j.castSucc)) =
        (⨅ j : Fin ρ, LinearMap.ker (L j)) := by
      rw [show (fun j : Fin ρ => LinearMap.ker (L' j.castSucc)) =
          (fun j : Fin ρ => LinearMap.ker (L j)) from funext fun j => by rw [hcast j]]
    have hlie : lieSub N ρ false M = ⨅ j : Fin (ρ + 1), LinearMap.ker (L' j) := by
      rw [hsplit, hInf, hlast]
      simp only [lieSub, L, Bool.false_eq_true, ite_false]
      rw [inf_comm]
    rw [ellW, hlie, finrank_span_sub_infi_ker_eq_rank w L']
    congr 1
    funext j k
    exact hL'val j k

end Work.BW

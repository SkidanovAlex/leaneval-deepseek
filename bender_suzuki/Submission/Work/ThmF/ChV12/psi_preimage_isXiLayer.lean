import Mathlib
import Submission.Work.Higman.typeB
import Submission.Work.Higman.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

/-- A line `F ∙ v` spanned by a non-zero vector has `|F|` elements: `c ↦ c • v` is a bijection
`F ≃ F ∙ v`. -/
lemma natCard_span_singleton {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    {v : M} (hv : v ≠ 0) :
    Nat.card ↥(Submodule.span F ({v} : Set M)) = Nat.card F := by
  have hinj : Function.Injective (fun c : F => c • v) := smul_left_injective F hv
  refine Nat.card_congr ?_
  refine ⟨fun w => Classical.choose (Submodule.mem_span_singleton.mp w.2),
          fun c => ⟨c • v, Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)⟩,
          ?_, ?_⟩
  · intro w
    exact Subtype.ext (Classical.choose_spec (Submodule.mem_span_singleton.mp w.2))
  · intro c
    apply hinj
    exact Classical.choose_spec (Submodule.mem_span_singleton.mp
      (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)))

-- Let `ψ : Q → F × F` be an additive map onto `F × F` (surjective), with kernel the centre
-- `Z(Q)` of a finite group `Q`, where `|F| = |Z(Q)|`; let `ψ` intertwine an automorphism `ξ`
-- of `Q` with multiplication by `λ ∈ Fˣ`.  Then for `v ≠ 0` the preimage `M = {x | ψ x ∈ F ∙ v}`
-- of the line `F ∙ v` is a subgroup of `Q` containing `Z(Q)`, of order `|Z(Q)|² = |F|²`, and
-- `ξ`-invariant: a `Work.Higman.IsXiLayer ξ` (`M` is the preimage of a line of
-- `Q/Z(Q) ≅ F × F`).
--
-- Proof.  `M` is a subgroup since `ψ` is additive (`ψ 1 = 0` and `ψ x⁻¹ = - ψ x` follow from
-- `hadd`); `Z(Q) = ker ψ ≤ M`; `ξ`-invariance since `F ∙ v` is closed under scaling.  For the
-- order: the restriction of `ψ` to `M` is onto `F ∙ v` with kernel `M ⊓ Z(Q) = Z(Q)`, so
-- `|M| = |Z(Q)| * |F ∙ v|` (`Subgroup.card_mul_index` + `Subgroup.index_ker`), and
-- `|F ∙ v| = |F|` for `v ≠ 0` since `c ↦ c • v` is a bijection `F ≃ F ∙ v`
-- (`Submodule.mem_span_singleton`, `Submodule.mem_span_singleton_self`).
theorem psi_preimage_isXiLayer {Q : Type} [Group Q] [Finite Q]
    {F : Type} [Field F] [Fintype F]
    (ψ : Q → F × F) (hadd : ∀ x y, ψ (x * y) = ψ x + ψ y)
    (hker : ∀ x : Q, ψ x = 0 ↔ x ∈ Subgroup.center Q)
    (hsurj : Function.Surjective ψ)
    (hcardF : Nat.card F = Nat.card ↥(Subgroup.center Q))
    {ξ : MulAut Q} {lam : Fˣ} (hlam : ∀ x : Q, ψ (ξ x) = (lam : F) • ψ x)
    {v : F × F} (hv : v ≠ 0) :
    ∃ M : Subgroup Q, (∀ x : Q, x ∈ M ↔ ψ x ∈ Submodule.span F ({v} : Set (F × F))) ∧
      Work.Higman.IsXiLayer ξ M := by
  -- `ψ` is additive, so `ψ 1 = 0` and `ψ x⁻¹ = - ψ x`.
  have hψ1 : ψ 1 = 0 := by
    have h := hadd 1 1
    rw [mul_one] at h
    have h2 := congrArg (fun t => t - ψ 1) h
    simpa using h2.symm
  have hψinv : ∀ x : Q, ψ x⁻¹ = - ψ x := by
    intro x
    have h := hadd x⁻¹ x
    rw [inv_mul_cancel] at h
    rw [hψ1] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  -- The line and its preimage under `ψ`.
  let V : Submodule F (F × F) := Submodule.span F ({v} : Set (F × F))
  let M : Subgroup Q :=
    { carrier := {x : Q | ψ x ∈ V},
      mul_mem' := by
        intro a b ha hb
        show ψ (a * b) ∈ V
        rw [hadd]
        exact V.add_mem ha hb,
      one_mem' := by
        show ψ 1 ∈ V
        rw [hψ1]
        exact V.zero_mem,
      inv_mem' := by
        intro a ha
        show ψ a⁻¹ ∈ V
        rw [hψinv]
        exact V.neg_mem ha }
  have hMV : ∀ x : Q, x ∈ M ↔ ψ x ∈ V := fun x => Iff.rfl
  have hcenter_le : Subgroup.center Q ≤ M := by
    intro x hx
    show ψ x ∈ V
    rw [(hker x).mpr hx]
    exact V.zero_mem
  have hxi_inv : ∀ x ∈ M, ξ x ∈ M := by
    intro x hx
    show ψ (ξ x) ∈ V
    rw [hlam]
    exact V.smul_mem (lam : F) ((hMV x).mp hx)
  -- The restriction of `ψ` to `M`, viewed as a multiplicative homomorphism into the (additive
  -- group) line `V`; it is surjective with kernel `Z(Q) ⊓ M = Z(Q)`.
  let g : ↥M →* Multiplicative ↥V :=
    { toFun := fun x => Multiplicative.ofAdd ⟨ψ (x : Q), (hMV (x : Q)).mp x.2⟩
      map_one' := by
        rw [ofAdd_eq_one]
        exact Subtype.ext (by simpa using hψ1)
      map_mul' := fun x y => by
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd]
        apply Subtype.ext
        show ψ ((x * y : ↥M) : Q) = ψ (x : Q) + ψ (y : Q)
        rw [Subgroup.coe_mul]
        exact hadd (x : Q) (y : Q) }
  have hsurj_g : Function.Surjective g := by
    intro w
    obtain ⟨x, hx⟩ := hsurj ((w.toAdd : ↥V) : F × F)
    have hxM : x ∈ M := (hMV x).mpr (by rw [hx]; exact w.toAdd.2)
    refine ⟨⟨x, hxM⟩, ?_⟩
    rw [← ofAdd_toAdd w]
    apply congrArg Multiplicative.ofAdd
    exact Subtype.ext hx
  have hrange_card : Nat.card ↥(g.range) = Nat.card ↥V := by
    rw [MonoidHom.range_eq_top.mpr hsurj_g]
    rw [Nat.card_congr (Subgroup.topEquiv (G := Multiplicative ↥V)).toEquiv]
    exact Nat.card_congr Multiplicative.toAdd
  have hcardK : Nat.card ↥(g.ker) = Nat.card ↥(Subgroup.center Q) := by
    have hker_g : g.ker = (Subgroup.center Q).comap (Subgroup.subtype M) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_comap]
      have h1 : (g x = 1) ↔ ψ (x : Q) = 0 := by
        rw [show g x = Multiplicative.ofAdd
              (⟨ψ (x : Q), (hMV (x : Q)).mp x.2⟩ : ↥V) from rfl]
        rw [ofAdd_eq_one]
        exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
      rw [h1, hker]
      exact Iff.rfl
    rw [hker_g]
    refine Nat.card_congr ?_
    refine ⟨fun x => ⟨(x.1 : Q), x.2⟩,
            fun z => ⟨⟨(z : Q), hcenter_le z.2⟩, z.2⟩, ?_, ?_⟩
    · intro x
      exact Subtype.ext (Subtype.ext rfl)
    · intro z
      exact Subtype.ext rfl
  have hcardM : Nat.card ↥M = Nat.card ↥(Subgroup.center Q) ^ 2 := by
    have hsplit : Nat.card ↥(g.ker) * Nat.card ↥(g.range) = Nat.card ↥M := by
      rw [← Subgroup.index_ker g]
      exact Subgroup.card_mul_index g.ker
    have hV : Nat.card ↥V = Nat.card F := natCard_span_singleton hv
    calc Nat.card ↥M = Nat.card ↥(g.ker) * Nat.card ↥(g.range) := hsplit.symm
      _ = Nat.card ↥(Subgroup.center Q) * Nat.card F := by rw [hcardK, hrange_card, hV]
      _ = Nat.card ↥(Subgroup.center Q) * Nat.card ↥(Subgroup.center Q) := by rw [hcardF]
      _ = Nat.card ↥(Subgroup.center Q) ^ 2 := (pow_two _).symm
  exact ⟨M, hMV, hcenter_le, hxi_inv, hcardM⟩

end Work.ThmF.ChV12

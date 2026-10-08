import Mathlib
import Submission.Work.Higman.Layers.exists_isInv_isCompl

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman.Q3

section Aux

variable {P : Type} [Group P] {A : Subgroup P} [A.Normal]

/-- If `A` contains the commutator subgroup of `P` then `P ⧸ A` is abelian. -/
theorem quotA_mul_comm' (hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A) (a b : P ⧸ A) : a * b = b * a := by
  refine Quotient.inductionOn a (fun x => ?_)
  refine Quotient.inductionOn b (fun y => ?_)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have key : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
    simp only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]
  rw [key]
  exact hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top y⁻¹) (Subgroup.mem_top x⁻¹))

end Aux

/-- **Twin cover (invariant complement).**  Let `A ⊴ P` with `P/A` elementary abelian (i.e.
`⁅P,P⁆ ≤ A` and every square of `P` lies in `A`), and let `D` be a subgroup with `A < D`.  If `ϑ`
is an automorphism of `P` of **odd** order preserving `A` and `D`, then `D/A` has a
`ϑ`-invariant complement in the `𝔽₂⟨ϑ⟩`-module `P/A`: there is `Y` with `A ≤ Y`,
`Y` `ϑ`-invariant, `D ⊓ Y = A` and `D ⊔ Y = ⊤`.  Moreover `Y` is normal in `P`.

This is Higman (1963) §6's "`G = XY`, where `X`, `Y` are of `ξ`-length 3" in the `C₄`
configuration: the two `ξ`-length-3 subgroups of a would-be `ξ`-length-4 Suzuki 2-group.
The `𝔽₂⟨ϑ⟩`-module `P/A` is completely reducible because `ϑ` has odd order (Maschke in
characteristic two). -/
theorem twin_cover_of_odd_order {P : Type} [Group P] [Finite P] {A D : Subgroup P}
    {ϑ : MulAut P} (hodd : Odd (orderOf ϑ))
    (hAinv : A.map (ϑ : MulAut P).toMonoidHom = A)
    (hDinv : D.map (ϑ : MulAut P).toMonoidHom = D)
    (hAn : A.Normal) (hAD : A < D)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ ≤ A)
    (hsq : ∀ x : P, x ^ 2 ∈ A) :
    ∃ Y : Subgroup P, Y.Normal ∧ Y.map (ϑ : MulAut P).toMonoidHom = Y ∧ A ≤ Y ∧
      D ⊓ Y = A ∧ D ⊔ Y = ⊤ := by
  classical
  haveI : A.Normal := hAn
  have hAleD : A ≤ D := le_of_lt hAD
  -- ## The quotient `P ⧸ A` is an elementary abelian `2`-group
  let Q := P ⧸ A
  have hQcomm : ∀ a b : Q, a * b = b * a := quotA_mul_comm' (A := A) hGs
  letI : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hQcomm }
  haveI hQfin : Finite Q :=
    Finite.of_surjective (QuotientGroup.mk' A) (QuotientGroup.mk'_surjective A)
  -- ## The `𝔽₂`-vector space `V = P/A`
  let V := Additive Q
  haveI : Finite V := hQfin
  have h2zero : ∀ v : V, 2 • v = 0 := by
    intro x
    obtain ⟨w, rfl⟩ : ∃ w : Q, Additive.ofMul w = x := ⟨Additive.toMul x, rfl⟩
    have hw : w * w = 1 := by
      refine Quotient.inductionOn w (fun u => ?_)
      show (QuotientGroup.mk' A) u * (QuotientGroup.mk' A) u = 1
      rw [← map_mul, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      simpa [pow_two] using hsq u
    calc 2 • (Additive.ofMul w) = Additive.ofMul w + Additive.ofMul w := two_nsmul _
      _ = Additive.ofMul (w * w) := ofMul_mul w w
      _ = 0 := by rw [hw]; rfl
  letI : Module (ZMod 2) V := AddCommGroup.zmodModule h2zero
  -- ## The automorphism of `Q` induced by `ϑ`
  let ξQ : Q ≃* Q := QuotientGroup.congr A A (ϑ : MulAut P) hAinv
  have ξQ_mk : ∀ x : P, ξQ (QuotientGroup.mk' A x) = QuotientGroup.mk' A (ϑ x) :=
    fun x => QuotientGroup.congr_mk' A A (ϑ : MulAut P) hAinv x
  have ξQ_pow_mk : ∀ (k : ℕ) (x : P),
      (ξQ ^ k) (QuotientGroup.mk' A x) = QuotientGroup.mk' A ((ϑ ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      calc (ξQ ^ (k + 1)) (QuotientGroup.mk' A x)
          = (ξQ ^ k) (ξQ (QuotientGroup.mk' A x)) := by rw [pow_succ]; rfl
        _ = (ξQ ^ k) (QuotientGroup.mk' A (ϑ x)) := by rw [ξQ_mk]
        _ = QuotientGroup.mk' A ((ϑ ^ k) (ϑ x)) := ih (ϑ x)
        _ = QuotientGroup.mk' A ((ϑ ^ (k + 1)) x) := by rw [pow_succ, MulAut.mul_apply]
  have hξQ_pow : ξQ ^ (orderOf ϑ) = 1 := by
    ext w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective A w
    rw [ξQ_pow_mk, pow_orderOf_eq_one]
    simp
  -- ## The induced `𝔽₂`-linear endomorphism of `V`
  let σlin : V →ₗ[ZMod 2] V := AddMonoidHom.toZModLinearMap 2 (ξQ.toAdditive : V →+ V)
  have htoMul_σlin : ∀ v : V, Additive.toMul (σlin v) = ξQ (Additive.toMul v) := fun v => rfl
  have hσlin_ofMul : ∀ w : Q, σlin (Additive.ofMul w) = Additive.ofMul (ξQ w) := fun w => rfl
  have σlin_pow_ofMul : ∀ (k : ℕ) (w : Q),
      (σlin ^ k) (Additive.ofMul w) = Additive.ofMul ((ξQ ^ k) w) := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [pow_succ', Module.End.mul_apply, ih]
      show ξQ.toAdditive (Additive.ofMul ((ξQ ^ k) w)) = Additive.ofMul ((ξQ ^ (k + 1)) w)
      rw [show (ξQ ^ (k + 1)) = ξQ * ξQ ^ k from pow_succ' ξQ k]
      rfl
  have hσlinD : σlin ^ (orderOf ϑ) = 1 := by
    ext v
    obtain ⟨w, rfl⟩ : ∃ w : Q, Additive.ofMul w = v := ⟨Additive.toMul v, rfl⟩
    rw [σlin_pow_ofMul, hξQ_pow, Module.End.one_apply]
    rfl
  -- ## The image of `D` in `V`
  let W : Subgroup Q := D.map (QuotientGroup.mk' A)
  let C : Submodule (ZMod 2) V :=
    { carrier := {v : V | Additive.toMul v ∈ W}
      add_mem' := by
        intro a b ha hb
        show Additive.toMul (a + b) ∈ W
        rw [toMul_add]; exact W.mul_mem ha hb
      zero_mem' := by show Additive.toMul (0 : V) ∈ W; exact W.one_mem
      smul_mem' := by
        intro c x hx
        rcases (by revert c; decide : c = 0 ∨ c = 1) with rfl | rfl
        · rw [zero_smul]; show Additive.toMul (0 : V) ∈ W; exact W.one_mem
        · rw [one_smul]; exact hx }
  have hCmem : ∀ v : V, v ∈ C ↔ Additive.toMul v ∈ W := fun v => Iff.rfl
  have hCinv : Work.Higman.Layers.IsInv σlin C := by
    intro v hv
    rw [hCmem] at hv ⊢
    obtain ⟨d, hdD, hd⟩ := Subgroup.mem_map.mp hv
    refine Subgroup.mem_map.mpr ⟨ϑ d, ?_, ?_⟩
    · have h1 := Subgroup.mem_map_of_mem (f := (ϑ : MulAut P).toMonoidHom) hdD
      rwa [hDinv] at h1
    · rw [htoMul_σlin, ← hd, ξQ_mk]
  -- ## Maschke: an invariant complement
  obtain ⟨C', hC'inv, hC'disj, hC'sup⟩ :=
    Work.Higman.Layers.exists_isInv_isCompl (σ := σlin) (D := orderOf ϑ) hodd hσlinD hCinv
  have hnpos : 0 < orderOf ϑ := orderOf_pos ϑ
  have hσlin_pow_inv : ∀ k : ℕ, Work.Higman.Layers.IsInv (σlin ^ k) C' := by
    intro k
    induction k with
    | zero => intro v hv; simpa using hv
    | succ k ih =>
      intro v hv
      rw [pow_succ', Module.End.mul_apply]
      exact hC'inv _ (ih v hv)
  have hσlin_inv_inv : Work.Higman.Layers.IsInv (σlin ^ (orderOf ϑ - 1)) C' :=
    hσlin_pow_inv _
  have hpowmul : σlin ^ (orderOf ϑ - 1) * σlin = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hnpos, hσlinD]
  have hσlininv_apply : ∀ v : V, (σlin ^ (orderOf ϑ - 1)) (σlin v) = v := by
    intro v
    have h := congrArg (fun (f : V →ₗ[ZMod 2] V) => f v) hpowmul
    simpa [Module.End.mul_apply] using h
  have hσlin_ofMul_inv : ∀ y : P,
      (σlin ^ (orderOf ϑ - 1)) (Additive.ofMul (QuotientGroup.mk' A y))
        = Additive.ofMul (QuotientGroup.mk' A (ϑ⁻¹ y)) := by
    intro y
    have h1 : σlin (Additive.ofMul (QuotientGroup.mk' A (ϑ⁻¹ y)))
        = Additive.ofMul (QuotientGroup.mk' A y) := by
      rw [hσlin_ofMul, ξQ_mk]
      simp
      all_goals first | rfl | (congr 1; simp)
    rw [← h1, hσlininv_apply]
  -- ## The complement subgroup `Y`
  let Yq : Subgroup Q :=
    { carrier := {q : Q | Additive.ofMul q ∈ C'}
      mul_mem' := by
        intro a b ha hb
        show Additive.ofMul (a * b) ∈ C'
        rw [ofMul_mul]; exact C'.add_mem ha hb
      one_mem' := by
        show Additive.ofMul (1 : Q) ∈ C'
        exact C'.zero_mem
      inv_mem' := by
        intro a ha
        show Additive.ofMul a⁻¹ ∈ C'
        rw [ofMul_inv]; exact C'.neg_mem ha }
  let Y : Subgroup P := Yq.comap (QuotientGroup.mk' A)
  have hYmem : ∀ x : P, x ∈ Y ↔ Additive.ofMul (QuotientGroup.mk' A x) ∈ C' := by
    intro x
    change QuotientGroup.mk' A x ∈ Yq ↔ Additive.ofMul (QuotientGroup.mk' A x) ∈ C'
    rfl
  have hAleY : A ≤ Y := by
    intro a ha
    rw [hYmem]
    have h1 : QuotientGroup.mk' A a = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact ha
    rw [h1]
    exact C'.zero_mem
  -- ## `Y` is `ϑ`-invariant
  have hYstep : ∀ x : P, x ∈ Y → ϑ x ∈ Y := by
    intro x hx
    rw [hYmem] at hx ⊢
    have h : Additive.ofMul (QuotientGroup.mk' A (ϑ x))
        = σlin (Additive.ofMul (QuotientGroup.mk' A x)) := by
      rw [hσlin_ofMul, ξQ_mk]
    rw [h]
    exact hC'inv _ hx
  have hYstep_inv : ∀ x : P, x ∈ Y → ϑ⁻¹ x ∈ Y := by
    intro x hx
    rw [hYmem] at hx ⊢
    rw [← hσlin_ofMul_inv x]
    exact hσlin_inv_inv _ hx
  have hYinv : Y.map (ϑ : MulAut P).toMonoidHom = Y := by
    refine le_antisymm ?_ ?_
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hYstep x hx
    · intro y hy
      rw [Subgroup.mem_map]
      refine ⟨ϑ⁻¹ y, hYstep_inv y hy, ?_⟩
      show ϑ ((ϑ⁻¹ : MulAut P) y) = y
      simp
  have hYN : Y.Normal := by
    have hYqN : Yq.Normal := Subgroup.normal_of_isMulCommutative Yq
    exact hYqN.comap (QuotientGroup.mk' A)
  -- ## `D ⊓ Y = A`
  have hDY : D ⊓ Y = A := by
    refine le_antisymm ?_ (le_inf hAleD hAleY)
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxD, hxY⟩ := hx
    have hxW : Additive.ofMul (QuotientGroup.mk' A x) ∈ C := by
      rw [hCmem]
      exact Subgroup.mem_map.mpr ⟨x, hxD, rfl⟩
    have hxC' : Additive.ofMul (QuotientGroup.mk' A x) ∈ C' := (hYmem x).mp hxY
    have hbot : Additive.ofMul (QuotientGroup.mk' A x) ∈ (⊥ : Submodule (ZMod 2) V) := by
      rw [← hC'disj, Submodule.mem_inf]
      exact ⟨hxW, hxC'⟩
    rw [Submodule.mem_bot] at hbot
    have hq1 : QuotientGroup.mk' A x = 1 := by simpa using hbot
    exact (QuotientGroup.eq_one_iff x).mp hq1
  -- ## `D ⊔ Y = ⊤`
  have hDYtop : D ⊔ Y = ⊤ := by
    refine le_antisymm le_top ?_
    intro x _
    have hv : Additive.ofMul (QuotientGroup.mk' A x) ∈ (⊤ : Submodule (ZMod 2) V) :=
      Submodule.mem_top
    rw [← hC'sup] at hv
    rw [Submodule.mem_sup] at hv
    obtain ⟨p, hp, q, hq, hpq⟩ := hv
    obtain ⟨d, hdD, hd⟩ := Subgroup.mem_map.mp ((hCmem p).mp hp)
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective A (Additive.toMul q)
    have hyY : y ∈ Y := by rw [hYmem, hy]; exact hq
    have hdyd : QuotientGroup.mk' A (d * y) = Additive.toMul (p + q) := by
      rw [map_mul, hd, hy, toMul_add]
    have hkey : QuotientGroup.mk' A (d * y) = QuotientGroup.mk' A x := by
      rw [hdyd, hpq]
      rfl
    have hmemA : (d * y)⁻¹ * x ∈ A := QuotientGroup.eq.mp hkey
    have hmem1 : d * y ∈ D ⊔ Y :=
      mul_mem ((le_sup_left : D ≤ D ⊔ Y) hdD) ((le_sup_right : Y ≤ D ⊔ Y) hyY)
    have hmem2 : (d * y)⁻¹ * x ∈ D ⊔ Y := (le_sup_left : D ≤ D ⊔ Y) (hAleD hmemA)
    have hx_eq : x = (d * y) * ((d * y)⁻¹ * x) := by group
    rw [hx_eq]
    exact mul_mem hmem1 hmem2
  exact ⟨Y, hYN, hYinv, hAleY, hDY, hDYtop⟩

end Work.Higman.Q3

import Mathlib
import Submission.Work.Hering.AppVIII.Defs
import Submission.Work.Hering.AppVIII.frobPowOfFourth
import Submission.Work.Hering.AppVIII.CTwoStepFacts
import Submission.Work.Hering.AppVIII.SemiLinDefs
import Submission.Work.Hering.AppVIII.cType_mixed
import Submission.Work.Hering.AppVIII.semiLin_solvable

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix VIII, Proposition 4: the stabiliser of `P₁` in `Aut C(n,ε)` is solvable

`C(n,ε)` (`n = 2s+1 ≥ 3`) is the Suzuki 2-group of type `C` of Higman's table, in the two-step
model (`Work.Higman.CType`), and `P₁ = π^{-1}(0 × K)` its index-two subgroup
(`Work.Hering.CTypeP1`).  We prove that the stabiliser `S` of `P₁` in `Aut C(n,ε)` is solvable:
`α ↦ fstFun α` (the induced map on `C/Z`) is a homomorphism into the permutations of `K × K`;
its kernel `N` is abelian (it consists of the maps `(u,z) ↦ (u, s(u) + z)`), while the image lies
in the solvable group `semiLin` of semilinear maps `(x,y) ↦ (a₁ Φ^i x, η x + a₂ Φ^i y)`
(`Work.Hering.AppVIII.semiLin`), by the coefficient computation of Peterfalvi, App. VIII,
Prop. 4 (the mixed terms of the identity `g (q x y) = q (f₁ x) (f₃ x + f₂ y)`).
-/

set_option autoImplicit false

noncomputable section

namespace Work.Hering.AppVIII

open Work.Higman

variable {s : ℕ} {ε : KC s}

/-- If the "anisotropy" hypothesis of `C(n,ε)` holds for `ε` then `ε ≠ 0`. -/
theorem epsilon_ne_zero_of_aniso (s : ℕ) {ε : KC s}
    (h : ∀ x y : KC s, x * (thetaC s x) + ε * (sqrtF (KC s) x * thetaC s (y * y)) + y * y = 0 →
      x = 0 ∧ y = 0) : ε ≠ 0 := by
  rintro rfl
  have h1 : (1 : KC s) * thetaC s 1 + 0 * (sqrtF (KC s) 1 * thetaC s (1 * 1)) + 1 * 1 = 0 := by
    simp only [map_one, mul_one, zero_mul, one_mul, add_zero, CharTwo.add_self_eq_zero]
  exact one_ne_zero (h 1 1 h1).1

/-- For `α` in the stabiliser of `P₁ = π^{-1}(0 × K)`, the induced map on `C/Z` preserves
`0 × K`. -/
theorem fstFun_zero_mem (hε : ε ≠ 0) (α : MulAut (CTypeC s ε))
    (hα : α ∈ stabilizerMulAut (P1C s ε)) (y : KC s) :
    (fstFun α (0, y)).1 = 0 :=
  (hα _).mpr rfl

/-- The restriction of `fstFun α` to `0 × K` maps onto `0 × K` (for `α` in the stabiliser
of `P₁`). -/
theorem fstFun_zero_surj (hε : ε ≠ 0) (α : MulAut (CTypeC s ε))
    (hα : α ∈ stabilizerMulAut (P1C s ε)) {v : KC s × KC s} (hv : v.1 = 0) :
    ∃ y : KC s, fstFun α (0, y) = v := by
  have hstab : ∀ y : KC s, (fstFun α (0, y)).1 = 0 := fstFun_zero_mem hε α hα
  let g : KC s → {w : KC s × KC s // w.1 = 0} := fun y => ⟨fstFun α (0, y), hstab y⟩
  have hinj : Function.Injective g := by
    intro y y' h
    have h2 : fstFun α (0, y) = fstFun α (0, y') := congrArg Subtype.val h
    have h3 := fstFun_injective hε α h2
    simpa using h3
  let e : KC s ≃ {w : KC s × KC s // w.1 = 0} :=
    { toFun := fun y => ⟨(0, y), rfl⟩
      invFun := fun w => w.1.2
      left_inv := by intro y; rfl
      right_inv := by intro w; exact Subtype.ext (Prod.ext w.2.symm rfl) }
  have hsurj : Function.Surjective g := (Finite.injective_iff_surjective_of_equiv e).mp hinj
  obtain ⟨y, hy⟩ := hsurj ⟨v, hv⟩
  exact ⟨y, congrArg Subtype.val hy⟩

/-- The first component of `fstFun α` on `K × 0` is injective (for `α` in the stabiliser
of `P₁`). -/
theorem fstFun_fst_injective (hε : ε ≠ 0) (α : MulAut (CTypeC s ε))
    (hα : α ∈ stabilizerMulAut (P1C s ε)) :
    Function.Injective (fun x : KC s => (fstFun α (x, 0)).1) := by
  intro x x' hxx'
  have h3 : fstFun α (x + x', 0) = fstFun α (x, 0) + fstFun α (x', 0) := by
    have h := fstFun_add hε α (x, 0) (x', 0)
    simpa using h
  have h2 : (fstFun α (x + x', 0)).1 = 0 := by
    rw [h3]
    show (fstFun α (x, 0)).1 + (fstFun α (x', 0)).1 = 0
    have hxx'' : (fstFun α (x, 0)).1 = (fstFun α (x', 0)).1 := hxx'
    rw [hxx'', AddExpTwo.add_self]
  obtain ⟨y, hy⟩ := fstFun_zero_surj hε α hα h2
  have h4 : (x + x', 0) = (0, y) := fstFun_injective hε α hy.symm
  have h5 : x + x' = 0 := by simpa using congrArg Prod.fst h4
  calc x = x + 0 := (add_zero x).symm
    _ = x + (x + x') := by rw [h5, add_zero]
    _ = x + x + x' := (add_assoc x x x').symm
    _ = x' := by rw [AddExpTwo.add_self, zero_add]

/-- The second component of `fstFun α` on `0 × K` is injective (for `α` in the stabiliser
of `P₁`). -/
theorem fstFun_snd_injective (hε : ε ≠ 0) (α : MulAut (CTypeC s ε))
    (hα : α ∈ stabilizerMulAut (P1C s ε)) :
    Function.Injective (fun y : KC s => (fstFun α (0, y)).2) := by
  intro y y' h
  have h1 : fstFun α (0, y) = fstFun α (0, y') := by
    refine Prod.ext ?_ ?_
    · rw [fstFun_zero_mem hε α hα y, fstFun_zero_mem hε α hα y']
    · exact h
  have h3 := fstFun_injective hε α h1
  simpa using h3

/-- `fstFun α` in coordinates: `(x,y) ↦ (f₁ x, f₃ x + f₂ y)` for `α` in the stabiliser. -/
theorem fstFun_coord (hε : ε ≠ 0) (α : MulAut (CTypeC s ε))
    (hα : α ∈ stabilizerMulAut (P1C s ε)) (x y : KC s) :
    fstFun α (x, y) = ((fstFun α (x, 0)).1, (fstFun α (x, 0)).2 + (fstFun α (0, y)).2) := by
  have hxy : fstFun α (x, y) = fstFun α (x, 0) + fstFun α (0, y) := by
    have h := fstFun_add hε α (x, 0) (0, y)
    simpa using h
  rw [hxy]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add, fstFun_zero_mem hε α hα y, add_zero]
  · rw [Prod.snd_add]

/-- The set of `fstFun α`, `α` in the stabiliser of `P₁`, is contained in `semiLin`. -/
theorem ofBijective_fstFun_mem_semiLin (hε : ε ≠ 0) (hs : 1 ≤ s) (α : MulAut (CTypeC s ε))
    (hα : α ∈ stabilizerMulAut (P1C s ε)) :
    (Equiv.ofBijective (fstFun α) (fstFun_bijective hε α)) ∈ semiLin (KC s) := by
  obtain ⟨i, a₁, a₂, ha₁, ha₂, hf₁, hf₂⟩ :=
    cType_mixed (s := s) hs (ε := ε) hε
      (fun x : KC s => (fstFun α (x, 0)).1) (fun y : KC s => (fstFun α (0, y)).2)
      (fun x : KC s => (fstFun α (x, 0)).2) (sndFun α)
      (fun x y => by
        have h := congrArg Prod.fst (fstFun_add hε α (x, 0) (y, 0))
        simpa using h)
      (fun x y => by
        have h := congrArg Prod.snd (fstFun_add hε α (0, x) (0, y))
        simpa using h)
      (fun x y => by
        have h := congrArg Prod.snd (fstFun_add hε α (x, 0) (y, 0))
        simpa using h)
      (sndFun_add hε α)
      (fstFun_fst_injective hε α hα) (fstFun_snd_injective hε α hα)
      (fun x y => by
        rw [sndFun_quadC]
        congr 1
        exact fstFun_coord hε α hα x y)
  refine ⟨a₁, a₂, ha₁, ha₂, (i : ℤ), fun x => (fstFun α (x, 0)).2, ?_⟩
  intro x y
  rw [Equiv.ofBijective_apply, fstFun_coord hε α hα x y, hf₁ x, hf₂ y]
  congr 1 <;> simp only [frobK, zpow_natCast, frobeniusEquiv_pow_apply]

/-- **App. VIII, Prop. 4.**  If the anisotropy hypothesis holds for `ε`, the stabiliser of `P₁`
in `Aut C(n,ε)` is solvable. -/
theorem isSolvable_stabilizer (hs : 1 ≤ s) {ε : KC s}
    (haniso : ∀ x y : KC s, x * (thetaC s x) + ε * (sqrtF (KC s) x * thetaC s (y * y)) +
      y * y = 0 → x = 0 ∧ y = 0) :
    Group.IsSolvable (stabilizerMulAut (CTypeP1 (thetaC s) ε)) := by
  have hε : ε ≠ 0 := epsilon_ne_zero_of_aniso s haniso
  let S : Subgroup (MulAut (CTypeC s ε)) := stabilizerMulAut (P1C s ε)
  have hbi : ∀ α : S, Function.Bijective (fstFun ((α : MulAut (CTypeC s ε)))) :=
    fun α => fstFun_bijective hε _
  let Φfun : S → Equiv.Perm (KC s × KC s) := fun α => Equiv.ofBijective _ (hbi α)
  have hΦmul : ∀ α β : S, Φfun (α * β) = Φfun α * Φfun β := by
    intro α β
    apply Equiv.ext
    intro u
    show Φfun (α * β) u = Φfun α (Φfun β u)
    simp only [Φfun, Equiv.ofBijective_apply]
    change fstFun (((α : MulAut (CTypeC s ε)) * (β : MulAut (CTypeC s ε)))) u =
      fstFun ((α : MulAut (CTypeC s ε))) (fstFun ((β : MulAut (CTypeC s ε))) u)
    rw [fstFun_mul hε]
    rfl
  have hΦone : Φfun 1 = 1 := by
    apply Equiv.ext
    intro u
    show Φfun 1 u = (1 : Equiv.Perm (KC s × KC s)) u
    simp only [Φfun, Equiv.ofBijective_apply, fstFun_one]
    rfl
  let Φ : S →* Equiv.Perm (KC s × KC s) :=
    { toFun := Φfun, map_one' := hΦone, map_mul' := hΦmul }
  have hfstN : ∀ a : Φ.ker, fstFun ((a : S) : MulAut (CTypeC s ε)) = id := by
    intro a
    have hmem : Φ (a : S) = 1 := MonoidHom.mem_ker.mp a.2
    funext u
    have h := congrArg (fun e : Equiv.Perm (KC s × KC s) => e u) hmem
    simpa [Φ, Φfun, Equiv.ofBijective_apply] using h
  have hNapply : ∀ (a : Φ.ker) (u : KC s × KC s) (z : KC s),
      (((a : S) : MulAut (CTypeC s ε)) ⟨u, z⟩) =
        ⟨u, (((a : S) : MulAut (CTypeC s ε)) ⟨u, 0⟩).snd + z⟩ := by
    intro a u z
    rw [alpha_apply hε, hfstN a, sndFun_eq_id hε _ (hfstN a)]
    rfl
  have hNcomm : ∀ a b : Φ.ker, a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    obtain ⟨u, z⟩ := x
    show (((a : S) : MulAut (CTypeC s ε)) (((b : S) : MulAut (CTypeC s ε)) ⟨u, z⟩)) =
      (((b : S) : MulAut (CTypeC s ε)) (((a : S) : MulAut (CTypeC s ε)) ⟨u, z⟩))
    rw [hNapply b u z]
    rw [hNapply a u ((((b : S) : MulAut (CTypeC s ε)) ⟨u, 0⟩).snd + z)]
    rw [hNapply a u z, hNapply b u ((((a : S) : MulAut (CTypeC s ε)) ⟨u, 0⟩).snd + z)]
    congr 1
    abel
  have hNsolv : Group.IsSolvable Φ.ker := Group.isSolvable_of_comm hNcomm
  have hmemS : ∀ α : S, Φfun α ∈ semiLin (KC s) := by
    intro α
    have hα : ((α : S) : MulAut (CTypeC s ε)) ∈ stabilizerMulAut (P1C s ε) := α.2
    have h := ofBijective_fstFun_mem_semiLin hε hs ((α : S) : MulAut (CTypeC s ε)) hα
    simpa [Φfun] using h
  have hsemiSolv : Group.IsSolvable (semiLin (KC s)) := semiLin_solvable (KC s)
  have hcod : ∀ y : S ⧸ Φ.ker,
      QuotientGroup.kerLift Φ y ∈ semiLin (KC s) := by
    intro y
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective Φ.ker y
    simpa [Φ, QuotientGroup.kerLift_mk] using hmemS α
  let Ψ : S ⧸ Φ.ker →* semiLin (KC s) :=
    MonoidHom.codRestrict (QuotientGroup.kerLift Φ) (semiLin (KC s)) hcod
  have hQ : Group.IsSolvable (S ⧸ Φ.ker) := by
    have hinj : Function.Injective Ψ := by
      intro y y' h
      exact QuotientGroup.kerLift_injective Φ (congrArg Subtype.val h)
    exact Group.isSolvable_of_isSolvable_injective hinj
  haveI := hNsolv
  haveI := hQ
  exact Group.isSolvable_of_subgroup_quotient Φ.ker

/-- **Appendix VIII, Proposition 4**: the stabiliser of `P₁` in `Aut C(n,ε)` is solvable. -/
theorem appVIIIProp4 : AppVIIIProp4 := by
  intro s ε hs haniso
  exact isSolvable_stabilizer (s := s) (ε := ε) hs haniso

end Work.Hering.AppVIII

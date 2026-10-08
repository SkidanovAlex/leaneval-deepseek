import Mathlib
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.higman_lemma2
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.false_of_sq_all_mem_powSub_two
import Submission.Work.Higman.exists_pow_four_hom
import Submission.Work.Higman.equivariant_bihom_trivial

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped commutatorElement

namespace Work.Higman.H8

variable {P : Type} [Group P] [Finite P]

/- ## The automorphism induced by `ξ` on an invariant subgroup -/

/-- The automorphism of `↥H` induced by `ξ` when `H` is `ξ`-invariant. -/
noncomputable def xiSubAut (h : IsSuzuki2Grp P) {H : Subgroup P}
    (hinv : H.map (h.xi : MulAut P).toMonoidHom = H) : MulAut ↥H where
  toFun x := ⟨h.xi (x : P), by
    have hx := Subgroup.mem_map_of_mem ((h.xi : MulAut P).toMonoidHom) x.2
    rwa [hinv] at hx⟩
  invFun x := ⟨(h.xi : MulAut P).symm (x : P),
    symm_mem_of_map_eq (h.xi : MulAut P) hinv x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

theorem xiSubAut_apply (h : IsSuzuki2Grp P) {H : Subgroup P}
    (hinv : H.map (h.xi : MulAut P).toMonoidHom = H) (x : ↥H) :
    ((xiSubAut h hinv x : ↥H) : P) = h.xi (x : P) := rfl

theorem xiSubAut_symm_apply (h : IsSuzuki2Grp P) {H : Subgroup P}
    (hinv : H.map (h.xi : MulAut P).toMonoidHom = H) (x : ↥H) :
    (((xiSubAut h hinv).symm x : ↥H) : P) = (h.xi : MulAut P).symm (x : P) := rfl

theorem xiSubAut_pow_apply (h : IsSuzuki2Grp P) {H : Subgroup P}
    (hinv : H.map (h.xi : MulAut P).toMonoidHom = H) (k : ℕ) (x : ↥H) :
    (((xiSubAut h hinv) ^ k) x : P) = (h.xi ^ k) (x : P) := by
  revert x
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih (xiSubAut h hinv x), xiSubAut_apply, pow_succ,
        MulAut.mul_apply]

/- ## Commutator calculus in `C`, a group of class two

`A ≤ C` centralises `C` and contains `[C,C] = A²`, so `C` has class two: commutators of
elements of `C` are central in `C`, and the usual identities hold. -/

/-- `C` has class two: its commutator subgroup is central. -/
theorem commutator_le_center_subtype {A C : Subgroup P}
    (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c) (hCd : ⁅C, C⁆ = powSub A 2) :
    ⁅(⊤ : Subgroup ↥C), ⊤⁆ ≤ Subgroup.center ↥C := by
  rw [Subgroup.commutator_le]
  intro u _ v _
  rw [Subgroup.mem_center_iff]
  intro w
  apply Subtype.ext
  have hmem : ((⁅u, v⁆ : ↥C) : P) ∈ A := by
    have hcoe : ((⁅u, v⁆ : ↥C) : P) = ⁅((u : ↥C) : P), ((v : ↥C) : P)⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe]
    have h1 : ⁅((u : ↥C) : P), ((v : ↥C) : P)⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator u.2 v.2
    rw [hCd] at h1
    exact powSub_le (by norm_num) h1
  have h2 := hZ _ w.2 _ hmem
  simpa using h2

/-- A commutator of two elements of `C` lies in `A` (and hence in `A²`). -/
theorem commutator_mem_A {A C : Subgroup P} (hCd : ⁅C, C⁆ = powSub A 2) {x y : P}
    (hx : x ∈ C) (hy : y ∈ C) : ⁅x, y⁆ ∈ A := by
  have h1 : ⁅x, y⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [hCd] at h1
  exact powSub_le (by norm_num) h1

/-- Commutators are unchanged by multiplying an argument by an element of `A` (left slot). -/
theorem commutator_mul_mem_left {A C : Subgroup P} (hAC : A ≤ C)
    (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c) (hCd : ⁅C, C⁆ = powSub A 2)
    {x y a : P} (hx : x ∈ C) (hy : y ∈ C) (ha : a ∈ A) :
    ⁅x * a, y⁆ = ⁅x, y⁆ := by
  have hZ2 := commutator_le_center_subtype (A := A) (C := C) hZ hCd
  have key : (⁅(⟨x, hx⟩ : ↥C) * (⟨a, hAC ha⟩ : ↥C), (⟨y, hy⟩ : ↥C)⁆ : ↥C) =
      (⁅(⟨x, hx⟩ : ↥C), (⟨y, hy⟩ : ↥C)⁆ * ⁅(⟨a, hAC ha⟩ : ↥C), (⟨y, hy⟩ : ↥C)⁆ : ↥C) :=
    commutator_mul_left hZ2 _ _ _
  have hone : (⁅(⟨a, hAC ha⟩ : ↥C), (⟨y, hy⟩ : ↥C)⁆ : ↥C) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_one]
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hZ y hy a ha]
    group
  have h := congrArg (fun t : ↥C => (t : P)) key
  rw [hone, mul_one] at h
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
  exact h

/-- Commutators are unchanged by multiplying an argument by an element of `A` (right slot). -/
theorem commutator_mul_mem_right {A C : Subgroup P} (hAC : A ≤ C)
    (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c) (hCd : ⁅C, C⁆ = powSub A 2)
    {x y a : P} (hx : x ∈ C) (hy : y ∈ C) (ha : a ∈ A) :
    ⁅x, y * a⁆ = ⁅x, y⁆ := by
  have hZ2 := commutator_le_center_subtype (A := A) (C := C) hZ hCd
  have h1 : ⁅y * a, x⁆ = ⁅y, x⁆ := by
    have key : (⁅(⟨y, hy⟩ : ↥C) * (⟨a, hAC ha⟩ : ↥C), (⟨x, hx⟩ : ↥C)⁆ : ↥C) =
        (⁅(⟨y, hy⟩ : ↥C), (⟨x, hx⟩ : ↥C)⁆ * ⁅(⟨a, hAC ha⟩ : ↥C), (⟨x, hx⟩ : ↥C)⁆ : ↥C) :=
      commutator_mul_left hZ2 _ _ _
    have hone : (⁅(⟨a, hAC ha⟩ : ↥C), (⟨x, hx⟩ : ↥C)⁆ : ↥C) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_one]
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hZ x hx a ha]
      group
    have h := congrArg (fun t : ↥C => (t : P)) key
    rw [hone, mul_one] at h
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
    exact h
  rw [show ⁅x, y * a⁆ = (⁅y * a, x⁆)⁻¹ by
        rw [commutatorElement_def, commutatorElement_def]; group,
      show ⁅x, y⁆ = (⁅y, x⁆)⁻¹ by
        rw [commutatorElement_def, commutatorElement_def]; group, h1]

/-- The commutator pairing is additive in the left slot (class two). -/
theorem commutator_mul_left' {A C : Subgroup P} (hAC : A ≤ C)
    (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c) (hCd : ⁅C, C⁆ = powSub A 2)
    {x y z : P} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hZ2 := commutator_le_center_subtype (A := A) (C := C) hZ hCd
  have key : (⁅(⟨x, hx⟩ : ↥C) * (⟨y, hy⟩ : ↥C), (⟨z, hz⟩ : ↥C)⁆ : ↥C) =
      (⁅(⟨x, hx⟩ : ↥C), (⟨z, hz⟩ : ↥C)⁆ * ⁅(⟨y, hy⟩ : ↥C), (⟨z, hz⟩ : ↥C)⁆ : ↥C) :=
    commutator_mul_left hZ2 _ _ _
  have h := congrArg (fun t : ↥C => (t : P)) key
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
  exact h

/-- The commutator pairing is additive in the right slot (class two). -/
theorem commutator_mul_right' {A C : Subgroup P} (hAC : A ≤ C)
    (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c) (hCd : ⁅C, C⁆ = powSub A 2)
    (hAab : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    {x y z : P} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have hm : ⁅y * z, x⁆ = ⁅y, x⁆ * ⁅z, x⁆ := commutator_mul_left' hAC hZ hCd hy hz hx
  have hcxz : ⁅x, z⁆ ∈ A := by
    rw [show ⁅x, z⁆ = (⁅z, x⁆)⁻¹ by rw [commutatorElement_def, commutatorElement_def]; group]
    exact A.inv_mem (commutator_mem_A hCd hz hx)
  have hcxy : ⁅x, y⁆ ∈ A := by
    rw [show ⁅x, y⁆ = (⁅y, x⁆)⁻¹ by rw [commutatorElement_def, commutatorElement_def]; group]
    exact A.inv_mem (commutator_mem_A hCd hy hx)
  have hcomm' : ⁅x, z⁆ * ⁅x, y⁆ = ⁅x, y⁆ * ⁅x, z⁆ := hAab _ hcxz _ hcxy
  rw [show ⁅x, y * z⁆ = (⁅y * z, x⁆)⁻¹ by
        rw [commutatorElement_def, commutatorElement_def]; group,
      hm, mul_inv_rev,
      show (⁅y, x⁆)⁻¹ = ⁅x, y⁆ by rw [commutatorElement_def, commutatorElement_def]; group,
      show (⁅z, x⁆)⁻¹ = ⁅x, z⁆ by rw [commutatorElement_def, commutatorElement_def]; group]
  exact hcomm'

/-! ## The main theorem -/

/-- **Cycle-free copy of `Work.Higman.xi_alt_pairing_false`.**

The result `Work.Higman.xi_alt_pairing_false` in
`Submission/Work/Higman/xi_alt_pairing_false.lean` is already proved and axiom-clean, but that
file imports `Submission.Work.Higman.no_square_of_maximal` (unused in its proof, but an import is
an import); other files import the present module, so this one must NOT import
`no_square_of_maximal`.  Concretely: copy the body of `xi_alt_pairing_false.lean` into this file
(it needs only `Defs`, `Basic`, `PowSub`, `SuzukiMaximal`, `suzuki_unipotence`, `higman_lemma2`,
`A_quot_irreducible`, `homogeneous_structure`, `false_of_sq_all_mem_powSub_two`,
`exists_pow_four_hom`, `equivariant_bihom_trivial`) and drop the offending import.

Statement: let `P` be a Suzuki 2-group, `A` a `ξ`-invariant abelian normal subgroup with
`A² = Ω₁(P) ≠ 1` and `A⁴ = 1`, and `C` a `ξ`-invariant normal subgroup with `A < C`, centralising
`A`, with `C² ≤ A` and `[C,C] = A²`, and no `ξ`-invariant normal subgroup strictly between `A`
and `C`. Then contradiction.

Route: the fourth power map `f : x ↦ x⁴` is a homomorphism `↥C →* ↥Ω₁(P)` (class two: `C`
centralises `A` and `[C,C] = A² ⊆ A`), its kernel `S` is normal in `P` and `ξ`-invariant with
`A ≤ S ≤ C`, so `S = A` or `S = C`; `S = C` contradicts Higman's Lemma 2
(`false_of_sq_all_mem_powSub_two`); `S = A` makes `f` surjective onto `Ω₁(P)`, and choosing for
`v ∈ Ω₁(P)` an element `root v ∈ C` with `(root v)⁴ = v` gives a `ξ`-equivariant alternating
biadditive `c : Ω₁ × Ω₁ → Ω₁` with `ξ` transitive on `Ω₁ \ {1}`, hence `c ≡ 0` by
Gorenstein–Thompson (`equivariant_bihom_trivial`), contradicting `[C,C] = A² ≠ 1`. -/

theorem alt_pairing_false {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : C ≠ A)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hOmega : Work.Higman.omega1 P = Work.Higman.powSub A 2)
    (hA2ne : Work.Higman.powSub A 2 ≠ ⊥)
    (hexp : ∀ a ∈ A, a ^ 4 = 1) :
    False := by
  classical
  -- ## Elementary facts about `V = A² = Ω₁(P)`
  have hVle : powSub A 2 ≤ A := powSub_le (by norm_num)
  have hVinv : (powSub A 2).map (h.xi : MulAut P).toMonoidHom = powSub A 2 :=
    map_powSub (h.xi : MulAut P) hA.map_eq 2
  have hOmA : ∀ z ∈ A, z ^ 2 = 1 → z ∈ powSub A 2 := by
    intro z _ hz2
    rw [← hOmega]
    exact h.mem_omega1.mpr hz2
  have hVsq : ∀ v ∈ powSub A 2, v ^ 2 = 1 := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := (mem_powSub_iff hA.abelian).mp hv
    rw [← pow_mul, show 2 * 2 = 4 from rfl]
    exact hexp a ha
  -- ## The fourth power map and its kernel `S`
  obtain ⟨f, hf, hfker⟩ := exists_pow_four_hom hAC hZ hC2 hCd hexp
  let S : Subgroup P := f.ker.map C.subtype
  have hSmem : ∀ x : P, x ∈ S ↔ x ∈ C ∧ x ^ 4 = 1 := by
    intro x
    constructor
    · intro hx
      change x ∈ Subgroup.map C.subtype f.ker at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hy1 : f y = 1 := MonoidHom.mem_ker.mp hy
      have h4 : (y : P) ^ 4 = 1 := by
        have hh := congrArg (fun t : ↥(powSub A 2) => (t : P)) hy1
        rw [Subgroup.coe_one, hf y] at hh
        exact hh
      exact ⟨by rw [← hyx]; exact y.2, by rw [← hyx]; exact h4⟩
    · intro hx
      obtain ⟨hxC, hx4⟩ := hx
      refine ⟨⟨x, hxC⟩, ?_, rfl⟩
      change f ⟨x, hxC⟩ = 1
      apply Subtype.ext
      rw [Subgroup.coe_one, hf]
      exact hx4
  have hSC : S ≤ C := fun x hx => ((hSmem x).mp hx).1
  have hAS : A ≤ S := fun a ha => (hSmem a).mpr ⟨hAC ha, hexp a ha⟩
  have hSn : S.Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    obtain ⟨hnC, hn4⟩ := (hSmem n).mp hn
    refine (hSmem (g * n * g⁻¹)).mpr ⟨hCn.conj_mem n hnC g, ?_⟩
    have hconj : g * n ^ 4 * g⁻¹ = (g * n * g⁻¹) ^ 4 := by
      have hh := map_pow (MulAut.conj g) n 4
      simpa [MulAut.conj_apply] using hh.symm
    rw [← hconj, hn4, mul_one, mul_inv_cancel]
  have hSinv : S.map (h.xi : MulAut P).toMonoidHom = S := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨hyC, hy4⟩ := (hSmem y).mp hy
      refine (hSmem (h.xi y)).mpr ⟨?_, ?_⟩
      · rw [← hCinv]; exact Subgroup.mem_map_of_mem _ hyC
      · rw [← map_pow, hy4, map_one]
    · intro x hx
      obtain ⟨hxC, hx4⟩ := (hSmem x).mp hx
      refine ⟨(h.xi : MulAut P).symm x, ?_, by simp⟩
      refine (hSmem ((h.xi : MulAut P).symm x)).mpr ⟨?_, ?_⟩
      · have h1 : x ∈ C.map (h.xi : MulAut P).toMonoidHom := by rw [hCinv]; exact hxC
        obtain ⟨y, hy, hyx⟩ := h1
        have h2 : (h.xi : MulAut P).symm x = y := by rw [← hyx]; simp
        rw [h2]; exact hy
      · have h4 := map_pow (h.xi : MulAut P).symm x 4
        rw [hx4, map_one] at h4
        exact h4.symm
  rcases hcover S hSn hSinv hAS hSC with hSA | hSCeq
  · -- ## Case `S = A`: the fourth power map is onto `V` and yields a `ξ`-form
    -- elements of `V` are fourth powers of elements of `C`
    have hcongA : ∀ x y : ↥C, f x = f y → ∃ a ∈ A, (x : P) = a * (y : P) := by
      intro x y hxy
      have h1 : (x : P) * (y : P)⁻¹ ∈ S := (hfker x y).mp hxy
      rw [hSA] at h1
      exact ⟨(x : P) * (y : P)⁻¹, h1, by group⟩
    have hfeq : ∀ x : ↥C, f (xiSubAut h hCinv x) = xiSubAut h hVinv (f x) := by
      intro x
      apply Subtype.ext
      have h1 : ((f (xiSubAut h hCinv x) : ↥(powSub A 2)) : P) = (h.xi (x : P)) ^ 4 := by
        rw [hf, xiSubAut_apply]
      have h2 : ((xiSubAut h hVinv (f x) : ↥(powSub A 2)) : P) = (h.xi (x : P)) ^ 4 := by
        rw [xiSubAut_apply, hf, map_pow]
      rw [h1, h2]
    -- `V` is an irreducible `⟨ξ⟩`-module
    have hVirr : ∀ T : Subgroup P, T ≤ powSub A 2 →
        T.map (h.xi : MulAut P).toMonoidHom = T → T = ⊥ ∨ T = powSub A 2 := by
      intro T hT hTinv
      have h1 : T ≤ A ⊓ omega1 P := le_inf (hT.trans hVle) (by rw [hOmega]; exact hT)
      rcases invariant_subgroup_inf_omega1 h A h1 hTinv with hb | htop
      · exact Or.inl hb
      · refine Or.inr ?_
        rw [htop, hOmega, inf_eq_right.mpr hVle]
    -- the range of the fourth power map is all of `V`
    let g : ↥C →* P := (powSub A 2).subtype.comp f
    have hg : ∀ x : ↥C, g x = (x : P) ^ 4 := by
      intro x
      show ((f x : ↥(powSub A 2)) : P) = (x : P) ^ 4
      rw [hf]
    have hgrange : ∀ y : P, y ∈ g.range ↔ ∃ x : ↥C, (x : P) ^ 4 = y := by
      intro y
      rw [MonoidHom.mem_range]
      constructor
      · rintro ⟨x, hx⟩; exact ⟨x, by rw [← hx, hg]⟩
      · rintro ⟨x, hx⟩; exact ⟨x, by rw [hg, hx]⟩
    have hgle : g.range ≤ powSub A 2 := by
      rintro y ⟨x, rfl⟩
      rw [hg]
      have hx2 : (x : P) ^ 2 ∈ A := hC2 (pow_mem_powSub (n := 2) x.2)
      have h4 : ((x : P) ^ 2) ^ 2 ∈ powSub A 2 := pow_mem_powSub (n := 2) hx2
      simpa [← pow_mul] using h4
    have hgfor : ∀ y ∈ g.range, h.xi y ∈ g.range := by
      intro y hy
      obtain ⟨x, hx⟩ := hy
      refine ⟨xiSubAut h hCinv x, ?_⟩
      rw [hg, xiSubAut_apply, ← hx, hg]
      exact (map_pow (h.xi : MulAut P) (x : P) 4).symm
    have hgback : ∀ y ∈ g.range, (h.xi : MulAut P).symm y ∈ g.range := by
      intro y hy
      obtain ⟨x, hx⟩ := hy
      refine ⟨(xiSubAut h hCinv).symm x, ?_⟩
      rw [hg, xiSubAut_symm_apply, ← hx, hg, map_pow]
    have hginv : g.range.map (h.xi : MulAut P).toMonoidHom = g.range := by
      apply le_antisymm
      · rintro y ⟨z, hz, rfl⟩
        exact hgfor z hz
      · intro y hy
        exact ⟨(h.xi : MulAut P).symm y, hgback y hy, by simp⟩
    have hgne : g.range ≠ ⊥ := by
      intro hbot
      refine hCA (le_antisymm ?_ hAC)
      intro u hu
      have h4 : u ^ 4 ∈ g.range := (hgrange _).mpr ⟨⟨u, hu⟩, rfl⟩
      rw [hbot] at h4
      have h4' : u ^ 4 = 1 := Subgroup.mem_bot.mp h4
      have huS : u ∈ S := (hSmem u).mpr ⟨hu, h4'⟩
      rwa [hSA] at huS
    have hgtop : g.range = powSub A 2 := by
      rcases hVirr _ hgle hginv with hb | htop
      · exact absurd hb hgne
      · exact htop
    have hsurj : ∀ v : ↥(powSub A 2), ∃ x : ↥C, f x = v := by
      intro v
      have hv : (v : P) ∈ g.range := by rw [hgtop]; exact v.2
      obtain ⟨x, hx⟩ := (hgrange _).mp hv
      exact ⟨x, Subtype.ext (by rw [hf]; exact hx)⟩
    -- ## The alternating form
    letI : CommGroup ↥(powSub A 2) :=
      { (inferInstance : Group ↥(powSub A 2)) with
        mul_comm := fun x y => Subtype.ext
          (hA.abelian x (powSub_le (by norm_num) x.2) y (powSub_le (by norm_num) y.2)) }
    let root : ↥(powSub A 2) → ↥C := fun v => Classical.choose (hsurj v)
    have hroot : ∀ v, f (root v) = v := fun v => Classical.choose_spec (hsurj v)
    have hmemV : ∀ u v : ↥(powSub A 2),
        ⁅((root u : ↥C) : P), ((root v : ↥C) : P)⁆ ∈ powSub A 2 := by
      intro u v
      have h1 : ⁅((root u : ↥C) : P), ((root v : ↥C) : P)⁆ ∈ ⁅C, C⁆ :=
        Subgroup.commutator_mem_commutator (root u).2 (root v).2
      rwa [hCd] at h1
    let c : ↥(powSub A 2) → ↥(powSub A 2) → ↥(powSub A 2) :=
      fun u v => ⟨⁅((root u : ↥C) : P), ((root v : ↥C) : P)⁆, hmemV u v⟩
    have hc : ∀ u v : ↥(powSub A 2),
        ((c u v : ↥(powSub A 2)) : P) = ⁅((root u : ↥C) : P), ((root v : ↥C) : P)⁆ :=
      fun _ _ => rfl
    have hswap : ∀ {e x : P}, e ∈ A → x ∈ C → e * x = x * e :=
      fun {e x} he hx => (hZ x hx e he).symm
    have hcong1 : ∀ a b : ↥(powSub A 2),
        ∃ e ∈ A, (root (a * b) : P) = e * ((root a : P) * (root b : P)) := by
      intro a b
      refine hcongA (root (a * b)) (root a * root b) ?_
      rw [hroot, map_mul, hroot, hroot]
    have hc_mul : ∀ a b d : ↥(powSub A 2), c (a * b) d = c a d * c b d := by
      intro a b d
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hc]
      obtain ⟨e, heA, heq⟩ := hcong1 a b
      have hra : (root a : P) ∈ C := (root a).2
      have hrb : (root b : P) ∈ C := (root b).2
      have hrd : (root d : P) ∈ C := (root d).2
      rw [heq, hswap heA (C.mul_mem hra hrb),
        commutator_mul_mem_left hAC hZ hCd (C.mul_mem hra hrb) hrd heA,
        commutator_mul_left' hAC hZ hCd hra hrb hrd]
    have hc_mul' : ∀ a b d : ↥(powSub A 2), c a (b * d) = c a b * c a d := by
      intro a b d
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hc]
      obtain ⟨e, heA, heq⟩ := hcong1 b d
      have hra : (root a : P) ∈ C := (root a).2
      have hrb : (root b : P) ∈ C := (root b).2
      have hrd : (root d : P) ∈ C := (root d).2
      rw [heq, hswap heA (C.mul_mem hrb hrd),
        commutator_mul_mem_right hAC hZ hCd hra (C.mul_mem hrb hrd) heA,
        commutator_mul_right' hAC hZ hCd hA.abelian hra hrb hrd]
    have hc_alt : ∀ a : ↥(powSub A 2), c a a = 1 := by
      intro a
      apply Subtype.ext
      simp only [hc, Subgroup.coe_one, commutatorElement_def]
      group
    have hc_eq : ∀ a b : ↥(powSub A 2), xiSubAut h hVinv (c a b) = c (xiSubAut h hVinv a) (xiSubAut h hVinv b) := by
      intro a b
      apply Subtype.ext
      simp only [hc, xiSubAut_apply]
      rw [show h.xi ⁅(root a : P), (root b : P)⁆ =
          ⁅h.xi (root a : P), h.xi (root b : P)⁆ from by
        rw [commutatorElement_def, commutatorElement_def]; simp [map_mul, map_inv]]
      have h1 : ∃ e ∈ A, h.xi (root a : P) = e * (root (xiSubAut h hVinv a) : P) := by
        have hh : f (xiSubAut h hCinv (root a)) = f (root (xiSubAut h hVinv a)) := by
          rw [hfeq, hroot, hroot]
        obtain ⟨e, heA, heq⟩ := hcongA (xiSubAut h hCinv (root a))
          (root (xiSubAut h hVinv a)) hh
        exact ⟨e, heA, by rwa [xiSubAut_apply] at heq⟩
      have h2 : ∃ e ∈ A, h.xi (root b : P) = e * (root (xiSubAut h hVinv b) : P) := by
        have hh : f (xiSubAut h hCinv (root b)) = f (root (xiSubAut h hVinv b)) := by
          rw [hfeq, hroot, hroot]
        obtain ⟨e, heA, heq⟩ := hcongA (xiSubAut h hCinv (root b))
          (root (xiSubAut h hVinv b)) hh
        exact ⟨e, heA, by rwa [xiSubAut_apply] at heq⟩
      obtain ⟨e, heA, heq⟩ := h1
      obtain ⟨e', he'A, he'q⟩ := h2
      have hra : (root (xiSubAut h hVinv a) : P) ∈ C := (root (xiSubAut h hVinv a)).2
      have hrb : (root (xiSubAut h hVinv b) : P) ∈ C := (root (xiSubAut h hVinv b)).2
      rw [heq, he'q, hswap heA hra, hswap he'A hrb]
      exact calc ⁅(root (xiSubAut h hVinv a) : P) * e,
            (root (xiSubAut h hVinv b) : P) * e'⁆
          = ⁅(root (xiSubAut h hVinv a) : P),
              (root (xiSubAut h hVinv b) : P) * e'⁆ :=
              commutator_mul_mem_left hAC hZ hCd hra (C.mul_mem hrb (hAC he'A)) heA
        _ = ⁅(root (xiSubAut h hVinv a) : P), (root (xiSubAut h hVinv b) : P)⁆ :=
              commutator_mul_mem_right hAC hZ hCd hra hrb he'A
    -- the `ξ`-action on `V` is transitive on the non-identity elements
    have hV2 : ∀ x : ↥(powSub A 2), x * x = 1 :=
      fun x => Subtype.ext (by simpa [pow_two] using hVsq x x.2)
    have hVtr : ∀ x y : ↥(powSub A 2), x ≠ 1 → y ≠ 1 →
        ∃ k : ℕ, ((xiSubAut h hVinv) ^ k) x = y := by
      intro x y hx1 hy1
      have hx2 : orderOf ((x : ↥(powSub A 2)) : P) = 2 := by
        refine orderOf_eq_two_of_mem_omega1 h ?_ ?_
        · rw [hOmega]; exact x.2
        · intro hc; exact hx1 (Subtype.ext hc)
      have hy2 : orderOf ((y : ↥(powSub A 2)) : P) = 2 := by
        refine orderOf_eq_two_of_mem_omega1 h ?_ ?_
        · rw [hOmega]; exact y.2
        · intro hc; exact hy1 (Subtype.ext hc)
      obtain ⟨k, hk⟩ := h.trans _ _ hx2 hy2
      exact ⟨k, Subtype.ext (by rw [xiSubAut_pow_apply]; exact hk)⟩
    -- Gorenstein--Thompson: the form is trivial
    have htriv := equivariant_bihom_trivial hV2 (xiSubAut h hVinv) hVtr c hc_mul hc_mul' hc_alt hc_eq
    -- hence every commutator in `C` is trivial
    have hbot : ⁅C, C⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro x hx y hy
      rw [Subgroup.mem_bot]
      have h1 : ((c (f ⟨x, hx⟩) (f ⟨y, hy⟩) : ↥(powSub A 2)) : P) = 1 := by
        rw [htriv (f ⟨x, hx⟩) (f ⟨y, hy⟩)]; rfl
      rw [hc] at h1
      obtain ⟨a, haA, ha⟩ := hcongA (root (f ⟨x, hx⟩)) ⟨x, hx⟩ (hroot (f ⟨x, hx⟩))
      obtain ⟨b, hbA, hb⟩ := hcongA (root (f ⟨y, hy⟩)) ⟨y, hy⟩ (hroot (f ⟨y, hy⟩))
      rw [ha, hb, hswap haA hx, hswap hbA hy,
        commutator_mul_mem_left hAC hZ hCd hx (C.mul_mem hy (hAC hbA)) haA,
        commutator_mul_mem_right hAC hZ hCd hx hy hbA] at h1
      exact h1
    rw [hCd] at hbot
    exact hA2ne hbot
  · -- ## Case `S = C`: Higman's Lemma 2 gives a contradiction
    refine false_of_sq_all_mem_powSub_two h hA hAC hCA hOmega hA2ne hZ ?_
    intro x hx
    have hxS : x ∈ S := by rw [hSCeq]; exact hx
    obtain ⟨-, hx4⟩ := (hSmem x).mp hxS
    refine hOmA (x ^ 2) (hC2 (pow_mem_powSub (n := 2) hx)) ?_
    rw [← pow_mul, show 2 * 2 = 4 from rfl]
    exact hx4


end Work.Higman.H8

import Mathlib
import Submission.Work.Kunneth.FlatGen
import Submission.Work.Kunneth.HomProd
import Submission.Work.Kunneth.FlatDefs
import Submission.Work.Kunneth.HomValue
import Submission.Work.Kunneth.flatBase

/-!
# The flat Künneth isomorphism, with its value rule on the summand generators

This file proves `Work.Kunneth.flatKunneth_exists`: for a chain complex `C` of `ℤ`-modules and a
family `M` of flat `ℤ`-modules, there is an isomorphism

`H_n (homTens C M) ≅ ⨁_{p+q=n} H_p(C) ⊗_ℤ M q`

which sends the class of the summand generator `iCycles u ⊗ m` to `[u] ⊗ m`
(`Work.Kunneth.flatHT`).  The isomorphism is exhibited as the composite

* `homQuotIso` : `H_n ≅ Z_n ⧸ B_n` (the computation rule `homQuotIso_apply`);
* the projection `cycToProdLin` onto `∏_{p+q=n} (ker ∂_p ⧸ im ∂_{p+1})`;
* the flat base change isomorphisms `Work.Kunneth.flatBase` in each bidegree;
* `DirectSum.linearEquivFunOnFintype`, `∏_{p+q=n} H_p(C) ⊗ M q ≅ ⨁_{p+q=n} H_p(C) ⊗ M q`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

variable (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)

/-! ## Component lemmas for the summand inclusions -/

theorem tpLof_apply_same {A B : ChainComplex (ModuleCat ℤ) ℕ} (n : ℕ) (i : tpIdx n)
    (v : tpSummand A B i.1.1 i.1.2) : tpLof A B n i v i = v := by
  rw [tpLof, DirectSum.lof_apply]

theorem tpLof_apply_of_ne {A B : ChainComplex (ModuleCat ℤ) ℕ} (n : ℕ) {i j : tpIdx n}
    (h : j ≠ i) (v : tpSummand A B i.1.1 i.1.2) : tpLof A B n i v j = 0 := by
  rw [tpLof]
  exact DFinsupp.single_eq_of_ne h

/-! ## The differential of `homTens C M` -/

theorem homTens_d_apply (n : ℕ) (x : tpX C (sumShift M) n) :
    ((homTens C M).d n (n - 1)).hom x = hIn C M n x := by
  rw [homTens_d_in C M n]; rfl

theorem cycKer_eq_ker_hIn (n : ℕ) :
    cycKer (homTens C M) n = LinearMap.ker (hIn C M n) := by
  unfold cycKer
  erw [homTens_d_in C M n]
  rfl

/-- The underlying element of a cycle of `homTens C M`, in the spelling of `tpX`. -/
def cycVal (n : ℕ) (x : ↥(cycKer (homTens C M) n)) : tpX C (sumShift M) n :=
  (x : ↥((homTens C M).X n))

theorem cycVal_val (n : ℕ) (x : ↥(cycKer (homTens C M) n)) :
    cycVal C M n x = (x : ↥((homTens C M).X n)) := rfl

/-- Membership in the boundaries of `homTens C M`, in the spelling of `hIn`. -/
theorem mem_homBnd_iff_range (n : ℕ) (x : ↥(cycKer (homTens C M) n)) :
    x ∈ homBnd (homTens C M) n ↔ cycVal C M n x ∈ LinearMap.range (hIn C M (n + 1)) := by
  rw [mem_homBnd_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (homTens_d_apply C M (n + 1) w).symm.trans hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, (homTens_d_apply C M (n + 1) w).trans hw⟩

/-! ## The componentwise projection of the cycles -/

/-- The denominator submodule of `hQuot`. -/
abbrev hQuotDen (p q : ℕ) : Submodule ℤ ↥(LinearMap.ker (hDIn C M p q)) :=
  (LinearMap.range (hDOut C M p q)).comap (LinearMap.ker (hDIn C M p q)).subtype

/-- The projection of the cycles of `homTens C M` onto the cycles of one summand. -/
def hCycProj' (n : ℕ) (pq : tpIdx n) :
    ↥(cycKer (homTens C M) n) →ₗ[ℤ] ↥(LinearMap.ker (hDIn C M pq.1.1 pq.1.2)) where
  toFun x := ⟨cycVal C M n x pq, by
    have hx : hIn C M n (cycVal C M n x) = 0 := by
      rw [← homTens_d_apply C M n (cycVal C M n x)]
      exact x.2
    exact (mem_hIn_ker_iff C M n (cycVal C M n x)).mp (LinearMap.mem_ker.mpr hx) pq⟩
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' c x := by apply Subtype.ext; rfl

theorem hCycProj'_val (n : ℕ) (pq : tpIdx n) (x : ↥(cycKer (homTens C M) n)) :
    ((hCycProj' C M n pq x : ↥(LinearMap.ker (hDIn C M pq.1.1 pq.1.2))) :
        tpSummand C (sumShift M) pq.1.1 pq.1.2) = cycVal C M n x pq := rfl

/-- The projection of the cycles of `homTens C M` onto the product of the quotients of the
summands' cycles. -/
def cycToProdLin (n : ℕ) :
    ↥(cycKer (homTens C M) n) →ₗ[ℤ] (∀ pq : tpIdx n, ↥(hQuot C M pq.1.1 pq.1.2)) :=
  LinearMap.pi (fun pq => (Submodule.mkQ (hQuotDen C M pq.1.1 pq.1.2)).comp
    (hCycProj' C M n pq))

theorem cycToProdLin_apply (n : ℕ) (x : ↥(cycKer (homTens C M) n)) (pq : tpIdx n) :
    cycToProdLin C M n x pq
      = (hQuotDen C M pq.1.1 pq.1.2).mkQ (hCycProj' C M n pq x) := rfl

/-! ## The value of the projection on the summand generators -/

theorem flatGen_apply_same (n p q : ℕ) (hpq : p + q = n) (u : ↥(C.cycles p))
    (m : ↥((sumShift M).X q)) :
    cycVal C M n (flatGen C M n p q hpq u m) ⟨(p, q), hpq⟩ = (C.iCycles p).hom u ⊗ₜ[ℤ] m := by
  show flatElem C M n p q hpq u m ⟨(p, q), hpq⟩ = (C.iCycles p).hom u ⊗ₜ[ℤ] m
  rw [flatElem]
  exact tpLof_apply_same (A := C) (B := sumShift M) n ⟨(p, q), hpq⟩
    ((C.iCycles p).hom u ⊗ₜ[ℤ] m)

theorem flatGen_apply_of_ne (n p q : ℕ) (hpq : p + q = n) (u : ↥(C.cycles p))
    (m : ↥((sumShift M).X q)) (i : tpIdx n) (h : i ≠ ⟨(p, q), hpq⟩) :
    cycVal C M n (flatGen C M n p q hpq u m) i = 0 := by
  show flatElem C M n p q hpq u m i = 0
  rw [flatElem]
  exact tpLof_apply_of_ne (A := C) (B := sumShift M) n h _

theorem cycToProdLin_flatGen_same (n p q : ℕ) (hpq : p + q = n) (u : ↥(C.cycles p))
    (m : ↥((sumShift M).X q)) :
    cycToProdLin C M n (flatGen C M n p q hpq u m) ⟨(p, q), hpq⟩
      = (hQuotDen C M p q).mkQ
          ⟨(C.iCycles p).hom u ⊗ₜ[ℤ] m, hDIn_tmul_cycle C M p q u m⟩ := by
  rw [cycToProdLin_apply]
  congr 1
  apply Subtype.ext
  rw [hCycProj'_val]
  exact flatGen_apply_same C M n p q hpq u m

theorem cycToProdLin_flatGen_of_ne (n p q : ℕ) (hpq : p + q = n) (u : ↥(C.cycles p))
    (m : ↥((sumShift M).X q)) (i : tpIdx n) (h : i ≠ ⟨(p, q), hpq⟩) :
    cycToProdLin C M n (flatGen C M n p q hpq u m) i = 0 := by
  rw [cycToProdLin_apply]
  have h0 : hCycProj' C M n i (flatGen C M n p q hpq u m) = 0 := by
    apply Subtype.ext
    rw [hCycProj'_val]
    exact flatGen_apply_of_ne C M n p q hpq u m i h
  rw [h0, map_zero]

/-! ## The kernel and the surjectivity of the projection -/

theorem ker_cycToProdLin (n : ℕ) :
    (cycToProdLin C M n).ker = homBnd (homTens C M) n := by
  ext x
  rw [LinearMap.mem_ker, mem_homBnd_iff_range C M n x, hIn_range_succ, mem_hProdSub]
  constructor
  · intro h pq
    have h' : cycToProdLin C M n x pq = 0 := by
      have := congrFun h pq
      simpa using this
    rw [cycToProdLin_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      hQuotDen, Submodule.mem_comap] at h'
    exact h'
  · intro hx
    funext pq
    show cycToProdLin C M n x pq = 0
    rw [cycToProdLin_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      hQuotDen, Submodule.mem_comap]
    exact hx pq

theorem cycToProdLin_surjective (n : ℕ) :
    Function.Surjective (cycToProdLin C M n) := by
  intro f
  have hf : ∀ pq : tpIdx n, ∃ y : ↥(LinearMap.ker (hDIn C M pq.1.1 pq.1.2)),
      (hQuotDen C M pq.1.1 pq.1.2).mkQ y = f pq := by
    intro pq
    exact Submodule.mkQ_surjective (hQuotDen C M pq.1.1 pq.1.2) (f pq)
  choose g hg using hf
  have hmem : hMk C M n (fun pq => (g pq : tpSummand C (sumShift M) pq.1.1 pq.1.2))
      ∈ cycKer (homTens C M) n := by
    rw [cycKer_eq_ker_hIn C M n, mem_hIn_ker_iff]
    intro pq
    rw [hMk_apply]
    exact (g pq).2
  refine ⟨⟨hMk C M n (fun pq => (g pq : tpSummand C (sumShift M) pq.1.1 pq.1.2)), hmem⟩, ?_⟩
  funext pq
  show cycToProdLin C M n ⟨_, _⟩ pq = f pq
  rw [cycToProdLin_apply]
  have hsub : hCycProj' C M n pq ⟨hMk C M n
      (fun pq => (g pq : tpSummand C (sumShift M) pq.1.1 pq.1.2)), hmem⟩ = g pq := by
    apply Subtype.ext
    rw [hCycProj'_val]
    show (hMk C M n (fun pq => (g pq : tpSummand C (sumShift M) pq.1.1 pq.1.2))) pq
      = (g pq : tpSummand C (sumShift M) pq.1.1 pq.1.2)
    rw [hMk_apply]
  rw [hsub]
  exact hg pq

/-! ## The value of `flatHT` on the summand generators -/

theorem flatHT_apply_same (n p q : ℕ) (hpq : p + q = n) (u : ↥(C.cycles p))
    (m : ↥((sumShift M).X q)) :
    (flatHT C M n p q hpq u m) ⟨(p, q), hpq⟩ = hHTensOf C M p q u m := by
  show tpLof (sumShift (fun p => C.homology p)) (sumShift M) n ⟨(p, q), hpq⟩
      ((C.homologyπ p).hom u ⊗ₜ[ℤ] m) ⟨(p, q), hpq⟩ = _
  rw [tpLof_apply_same]
  rfl

theorem flatHT_apply_of_ne (n p q : ℕ) (hpq : p + q = n) (u : ↥(C.cycles p))
    (m : ↥((sumShift M).X q)) (i : tpIdx n) (h : i ≠ ⟨(p, q), hpq⟩) :
    (flatHT C M n p q hpq u m) i = 0 := by
  show tpLof (sumShift (fun p => C.homology p)) (sumShift M) n ⟨(p, q), hpq⟩
      ((C.homologyπ p).hom u ⊗ₜ[ℤ] m) i = 0
  exact tpLof_apply_of_ne (A := sumShift (fun p => C.homology p)) (B := sumShift M) n h _

/-- The direct sum `⨁_{p+q=n} H_p(C) ⊗ M q`, in the spelling of `DirectSum`. -/
abbrev dsumHT (n : ℕ) : Type := tpX (sumShift (fun p => C.homology p)) (sumShift M) n

/-- The summand `H_p(C) ⊗ M q`, in the spelling of `tpSummand`. -/
abbrev htSummand (p q : ℕ) : Type :=
  tpSummand (sumShift (fun p => C.homology p)) (sumShift M) p q

/-- The value of the inverse of `DirectSum.linearEquivFunOnFintype` on the components. -/
theorem symm_linearEquivFunOnFintype_apply (n : ℕ)
    (f : ∀ pq : tpIdx n, htSummand C M pq.1.1 pq.1.2) (i : tpIdx n) :
    ((DirectSum.linearEquivFunOnFintype ℤ (tpIdx n)
        (fun pq => htSummand C M pq.1.1 pq.1.2)).symm f) i = f i := by
  have h := LinearEquiv.apply_symm_apply (DirectSum.linearEquivFunOnFintype ℤ (tpIdx n)
    (fun pq => htSummand C M pq.1.1 pq.1.2)) f
  have h2 := congrFun h i
  rwa [DirectSum.linearEquivFunOnFintype_apply] at h2

/-! ## The main theorem -/

theorem flatKunneth_exists (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)
    (hM : ∀ q, Module.Flat ℤ ↥(M q)) (n : ℕ) :
    ∃ E : (Work.Kunneth.homTens C M).homology n ≅
        (Work.Kunneth.tpC (Work.Kunneth.sumShift (fun p => C.homology p))
          (Work.Kunneth.sumShift M)).X n,
      ∀ (p q : ℕ) (hpq : p + q = n) (u : ↥(C.cycles p)) (m : ↥((Work.Kunneth.sumShift M).X q)),
        E.hom.hom ((Work.Kunneth.homTens C M).homologyπ n
            (Work.Kunneth.cycleOf (Work.Kunneth.homTens C M) n
              (Work.Kunneth.flatGen C M n p q hpq u m)))
          = Work.Kunneth.flatHT C M n p q hpq u m := by
  have hψker : (cycToProdLin C M n).ker = homBnd (homTens C M) n := ker_cycToProdLin C M n
  have hψsurj : Function.Surjective (cycToProdLin C M n) := cycToProdLin_surjective C M n
  set e2Lin : (↥(cycKer (homTens C M) n) ⧸ homBnd (homTens C M) n) ≃ₗ[ℤ]
      (∀ pq : tpIdx n, ↥(hQuot C M pq.1.1 pq.1.2)) :=
    (Submodule.quotEquivOfEq (homBnd (homTens C M) n) (cycToProdLin C M n).ker
        hψker.symm).trans
      (LinearMap.quotKerEquivOfSurjective (cycToProdLin C M n) hψsurj) with he2def
  have he2 : ∀ x : ↥(cycKer (homTens C M) n),
      e2Lin ((homBnd (homTens C M) n).mkQ x) = cycToProdLin C M n x := by
    intro x
    rw [he2def, LinearEquiv.trans_apply, Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective]
    simp [LinearMap.quotKerEquivRange_apply_mk]
  set e3Lin : (∀ pq : tpIdx n, ↥(hQuot C M pq.1.1 pq.1.2)) ≃ₗ[ℤ]
      (∀ pq : tpIdx n, htSummand C M pq.1.1 pq.1.2) :=
    LinearEquiv.piCongrRight (fun pq => (hIsoToLinearEquiv ((flatBase C M hM pq.1.1
      pq.1.2).choose) : ↥(hQuot C M pq.1.1 pq.1.2) ≃ₗ[ℤ] htSummand C M pq.1.1 pq.1.2))
      with he3def
  set e4Lin : (∀ pq : tpIdx n, htSummand C M pq.1.1 pq.1.2) ≃ₗ[ℤ] dsumHT C M n :=
    (DirectSum.linearEquivFunOnFintype ℤ (tpIdx n)
      (fun pq => htSummand C M pq.1.1 pq.1.2)).symm with he4def
  have h34 : ∀ (g : ∀ pq : tpIdx n, ↥(hQuot C M pq.1.1 pq.1.2)) (i : tpIdx n),
      (e4Lin (e3Lin g)) i = ((flatBase C M hM i.1.1 i.1.2).choose).hom.hom (g i) := by
    intro g i
    rw [he4def, he3def, symm_linearEquivFunOnFintype_apply C M n,
      LinearEquiv.piCongrRight_apply]
    rfl
  set Elin : ↥((homTens C M).homology n) ≃ₗ[ℤ] dsumHT C M n :=
    (hIsoToLinearEquiv (homQuotIso (homTens C M) n)).trans
      (e2Lin.trans (e3Lin.trans e4Lin)) with hElin
  refine ⟨LinearEquiv.toModuleIso Elin, ?_⟩
  intro p q hpq u m
  have h1 : (hIsoToLinearEquiv (homQuotIso (homTens C M) n))
      ((homTens C M).homologyπ n
        (cycleOf (homTens C M) n (flatGen C M n p q hpq u m)))
      = (homBnd (homTens C M) n).mkQ (flatGen C M n p q hpq u m) := by
    show (homQuotIso (homTens C M) n).hom.hom ((homTens C M).homologyπ n
      (cycleOf (homTens C M) n (flatGen C M n p q hpq u m))) = _
    have hcyc : (cycIso (homTens C M) n).hom
        (cycleOf (homTens C M) n (flatGen C M n p q hpq u m))
        = flatGen C M n p q hpq u m := by
      rw [cycleOf_eq]
      exact homIso_hom_apply (cycIso (homTens C M) n) (flatGen C M n p q hpq u m)
    rw [homQuotIso_apply (homTens C M) n
      (cycleOf (homTens C M) n (flatGen C M n p q hpq u m)), hcyc]
  have hθ : ∀ (u' : ↥(C.cycles p)) (m' : ↥((sumShift M).X q))
      (h : hDIn C M p q ((C.iCycles p).hom u' ⊗ₜ[ℤ] m') = 0),
      ((flatBase C M hM p q).choose).hom.hom (hQuotOf C M p q u' m' h)
        = hHTensOf C M p q u' m' :=
    fun u' m' h => (flatBase C M hM p q).choose_spec u' m' h
  show e4Lin (e3Lin (e2Lin ((hIsoToLinearEquiv (homQuotIso (homTens C M) n))
      ((homTens C M).homologyπ n
        (cycleOf (homTens C M) n (flatGen C M n p q hpq u m)))))) = flatHT C M n p q hpq u m
  rw [h1, he2]
  apply DFinsupp.ext
  intro i
  rw [h34 (cycToProdLin C M n (flatGen C M n p q hpq u m)) i]
  by_cases hi : i = ⟨(p, q), hpq⟩
  · subst hi
    rw [cycToProdLin_flatGen_same, flatHT_apply_same]
    exact hθ u m (hDIn_tmul_cycle C M p q u m)
  · rw [cycToProdLin_flatGen_of_ne C M n p q hpq u m i hi,
      flatHT_apply_of_ne C M n p q hpq u m i hi, map_zero]

end

end Work.Kunneth

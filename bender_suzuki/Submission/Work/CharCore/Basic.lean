import Submission.Work.CharCore.CFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Elementary API for `Work.CharCore.Irr`, `IsChar`, `IsVChar`
-/

noncomputable section

open Classical Finset

namespace Work.CharCore

variable {G : Type*} [Group G] [Fintype G]

section Irr

theorem mem_Irr_iff_exists (χ : G → ℂ) :
    χ ∈ Irr G ↔ ∃ N ∈ irrSubmodules G, (submoduleRep N).character = χ := by
  simp [Irr]

/-- Every irreducible character is the character of one of the chosen simple submodules of
the regular module. -/
theorem exists_mem_irrSubmodules_of_mem_Irr {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    ∃ N ∈ irrSubmodules G, (submoduleRep N).character = χ :=
  (mem_Irr_iff_exists χ).mp hχ

/-- Every element of `Irr G` is a class function. -/
theorem isClassFun_of_mem_Irr {χ : G → ℂ} (hχ : χ ∈ Irr G) : IsClassFun χ := by
  obtain ⟨N, -, rfl⟩ := (mem_Irr_iff_exists χ).mp hχ
  exact isClassFun_character _

/-- The degree of an irreducible character is a natural number. -/
theorem exists_natCast_apply_one {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    ∃ d : ℕ, χ 1 = (d : ℂ) := by
  obtain ⟨N, -, rfl⟩ := (mem_Irr_iff_exists χ).mp hχ
  exact ⟨_, Representation.char_one _⟩

/-- An irreducible character is never zero. -/
theorem mem_Irr_ne_zero {χ : G → ℂ} (hχ : χ ∈ Irr G) : χ ≠ 0 := by
  intro h
  obtain ⟨N, hN, hNχ⟩ := exists_mem_irrSubmodules_of_mem_Irr hχ
  haveI := isSimpleModule_of_mem_irrSubmodules N hN
  have hnt : Nontrivial N := IsSimpleModule.nontrivial (groupAlgebra G) N
  have hpos : 0 < Module.finrank ℂ N := Module.finrank_pos_iff.mpr hnt
  have h1 : ((Module.finrank ℂ N : ℕ) : ℂ) = 0 := by
    rw [← Representation.char_one (submoduleRep N), hNχ]
    simp [h]
  exact (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)) h1

/-- `irrDeg` computes the value at `1` of an irreducible character. -/
theorem irrDeg_spec {χ : G → ℂ} (hχ : χ ∈ Irr G) : χ 1 = (irrDeg χ : ℂ) := by
  have h : ∃ d : ℕ, χ 1 = (d : ℂ) := exists_natCast_apply_one hχ
  rw [irrDeg, dif_pos h]
  exact Classical.choose_spec h

/-- `irrDeg` of an irreducible character is the dimension of the corresponding simple module. -/
theorem irrDeg_eq_finrank {χ : G → ℂ} (hχ : χ ∈ Irr G) {N : Submodule (groupAlgebra G) (groupAlgebra G)}
    (hN : N ∈ irrSubmodules G) (hNχ : (submoduleRep N).character = χ) :
    irrDeg χ = Module.finrank ℂ N := by
  have : (irrDeg χ : ℂ) = (Module.finrank ℂ N : ℕ) := by
    rw [← irrDeg_spec hχ, ← hNχ, Representation.char_one]
  exact Nat.cast_inj.mp this

/-- Irreducible characters have positive degree. -/
theorem irrDeg_pos {χ : G → ℂ} (hχ : χ ∈ Irr G) : 0 < irrDeg χ := by
  obtain ⟨N, hN, hNχ⟩ := exists_mem_irrSubmodules_of_mem_Irr hχ
  haveI := isSimpleModule_of_mem_irrSubmodules N hN
  have hnt : Nontrivial N := IsSimpleModule.nontrivial (groupAlgebra G) N
  have hpos : 0 < Module.finrank ℂ N := Module.finrank_pos_iff.mpr hnt
  rw [irrDeg_eq_finrank hχ hN hNχ]
  exact hpos

theorem irrDeg_pos' {χ : G → ℂ} (hχ : χ ∈ Irr G) : (irrDeg χ : ℝ) > 0 :=
  Nat.cast_pos.mpr (irrDeg_pos hχ)

theorem irrDeg_ne_zero {χ : G → ℂ} (hχ : χ ∈ Irr G) : (irrDeg χ : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (irrDeg_pos hχ))

end Irr

/-- The character of the regular representation is a class function. -/
theorem isClassFun_regularChar (G : Type*) [Group G] [Fintype G] : IsClassFun (regularChar G) := by
  intro g h
  by_cases hg : g = 1
  · subst hg; simp [regularChar]
  · have hne : h * g * h⁻¹ ≠ 1 := by
      intro hc
      apply hg
      have hh := congr_arg (fun x => h⁻¹ * x * h) hc
      simpa [mul_assoc] using hh
    simp [regularChar, hg, hne]

@[simp] theorem mem_charKernel {χ : G → ℂ} {g : G} : g ∈ charKernel χ ↔ χ g = χ 1 := Iff.rfl

section ClassFunSubmodule

/-- The space of class functions on `G`, as a submodule of all functions `G → ℂ`. -/
def classFunSubmodule (G : Type*) [Group G] [Fintype G] : Submodule ℂ (G → ℂ) where
  carrier := {f | IsClassFun f}
  zero_mem' := isClassFun_zero
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c _ hf => hf.smul c

@[simp] theorem mem_classFunSubmodule {f : G → ℂ} :
    f ∈ classFunSubmodule G ↔ IsClassFun f := Iff.rfl

end ClassFunSubmodule

section CharAPI

theorem IsChar.zero : IsChar (0 : G → ℂ) := AddSubmonoid.zero_mem _

theorem IsChar.of_mem_Irr {χ : G → ℂ} (hχ : χ ∈ Irr G) : IsChar χ :=
  AddSubmonoid.subset_closure hχ

theorem IsChar.add {f g : G → ℂ} (hf : IsChar f) (hg : IsChar g) : IsChar (f + g) :=
  AddSubmonoid.add_mem _ hf hg

theorem IsChar.nsmul {f : G → ℂ} (hf : IsChar f) (n : ℕ) : IsChar (n • f) :=
  AddSubmonoid.nsmul_mem _ hf n

theorem IsChar.sum {ι : Type*} {s : Finset ι} {f : ι → G → ℂ}
    (h : ∀ i ∈ s, IsChar (f i)) : IsChar (∑ i ∈ s, f i) :=
  AddSubmonoid.sum_mem _ h

theorem IsVChar.zero : IsVChar (0 : G → ℂ) := AddSubgroup.zero_mem _

theorem IsVChar.of_mem_Irr {χ : G → ℂ} (hχ : χ ∈ Irr G) : IsVChar χ :=
  AddSubgroup.subset_closure hχ

theorem IsVChar.add {f g : G → ℂ} (hf : IsVChar f) (hg : IsVChar g) : IsVChar (f + g) :=
  AddSubgroup.add_mem _ hf hg

theorem IsVChar.neg {f : G → ℂ} (hf : IsVChar f) : IsVChar (-f) := AddSubgroup.neg_mem _ hf

theorem IsVChar.sub {f g : G → ℂ} (hf : IsVChar f) (hg : IsVChar g) : IsVChar (f - g) :=
  AddSubgroup.sub_mem _ hf hg

theorem IsVChar.zsmul {f : G → ℂ} (hf : IsVChar f) (n : ℤ) : IsVChar (n • f) :=
  AddSubgroup.zsmul_mem _ hf n

theorem IsVChar.sum {ι : Type*} {s : Finset ι} {f : ι → G → ℂ}
    (h : ∀ i ∈ s, IsVChar (f i)) : IsVChar (∑ i ∈ s, f i) :=
  AddSubgroup.sum_mem _ h

theorem IsChar.toVChar {f : G → ℂ} (hf : IsChar f) : IsVChar f :=
  AddSubmonoid.closure_le.mpr (fun _ hx => AddSubgroup.subset_closure hx) hf


theorem IsChar.isClassFun {f : G → ℂ} (hf : IsChar f) : IsClassFun f := by
  induction hf using AddSubmonoid.closure_induction with
  | mem x hx => exact isClassFun_of_mem_Irr hx
  | zero => exact isClassFun_zero
  | add x y _ _ hx hy => exact hx.add hy

theorem IsVChar.isClassFun {f : G → ℂ} (hf : IsVChar f) : IsClassFun f := by
  induction hf using AddSubgroup.closure_induction with
  | mem x hx => exact isClassFun_of_mem_Irr hx
  | zero => exact isClassFun_zero
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg

end CharAPI

end Work.CharCore

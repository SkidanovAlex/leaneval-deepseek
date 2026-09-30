import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

/-!
# The E¹ and E² pages of a filtered chain complex

This file sets up the (first) page of the spectral sequence of a filtration of a chain complex of
`ℤ`-modules, in the concrete form needed for the integral Serre spectral sequence (area SSS).

* `Work.SSSR.Filtration C` — a saturated filtration of `C` by subcomplexes `F s` (`s : ℕ`), with
  `F_{-1} = 0` built in as the convention `grF F 0 = F 0`.
* `Work.SSSR.grF ξ s = F_s/F_{s-1}` (with `grF ξ 0 = F_0`), `E1 ξ s t = H_{s+t}(grF ξ s)`.
* `Work.SSSR.d1 ξ s t : E¹_{s+1,t} → E¹_{s,t}` is the composite `j ≫ k` of the exact couple of the
  filtration (`k` the connecting map of `0 → F_s → F_{s+1} → F_{s+1}/F_s → 0` and `j` the map
  induced by `F_s → F_s/F_{s-1}`).  With this definition `d¹ ≫ d¹ = 0` follows *immediately* from
  the exactness `H(F_{s+1}) → H(F_{s+1}/F_s) → H(F_s)` (`ShortComplex.ShortExact.comp_δ`).
* `Work.SSSR.E2 ξ s t = H_s(E¹_{*,t})` is the E² page.
* `Work.SSSR.Phi ξ n s ⊆ H_n(C)` is the image filtration `im(H_n(F_s) → H_n(C))`.

No spectral sequence API of Mathlib is used; the whole file is elementary homology algebra.
-/

set_option autoImplicit false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits
noncomputable section

/-- The inclusion `F_s ⟶ F_{s+1}` of consecutive terms of a filtration. -/
def incF (F : ℕ ⥤ ChainComplex (ModuleCat R) ℕ) (s : ℕ) : F.obj s ⟶ F.obj (s + 1) :=
  F.map (homOfLE (Nat.le_succ s))

/-- The graded piece: `grF F 0 = F_0` (i.e. `F_0/F_{-1}` where `F_{-1} = 0`), and
`grF F (s+1) = F_{s+1}/F_s`. -/
def grF (F : ℕ ⥤ ChainComplex (ModuleCat R) ℕ) : ℕ → ChainComplex (ModuleCat R) ℕ
  | 0 => F.obj 0
  | (s + 1) => cokernel (incF F s)

@[simp] theorem grF_zero (F : ℕ ⥤ ChainComplex (ModuleCat R) ℕ) : grF F 0 = F.obj 0 := rfl

@[simp] theorem grF_succ (F : ℕ ⥤ ChainComplex (ModuleCat R) ℕ) (s : ℕ) :
    grF F (s + 1) = cokernel (incF F s) := rfl

/-- A **saturated filtration** of a chain complex `C` by subcomplexes `F s`, `s : ℕ`.

* `mono` : the terms are nested (`F_s ⊆ F_{s+1}`),
* `incl` : the inclusion of `F s` into the total complex `C`,
* `sat`  : the filtration is *saturated*: `F_n` contains all `n`-chains of `C`, i.e. the inclusion
  is an isomorphism in degree `n`.  This is the condition `F_n C_n = C_n` which makes the
  filtration finite in each degree (`Φ_n = H_n(C)`). -/
structure Filtration (R : Type) [CommRing R] [Nontrivial R] (C : ChainComplex (ModuleCat R) ℕ) where
  /-- the terms of the filtration -/
  F : ℕ ⥤ ChainComplex (ModuleCat R) ℕ
  /-- consecutive inclusions are monomorphisms -/
  mono : ∀ s, Mono (incF F s)
  /-- the inclusion of a term into the total complex -/
  incl : ∀ s, F.obj s ⟶ C
  mono_incl : ∀ s, Mono (incl s)
  compat : ∀ {s t : ℕ} (h : s ≤ t), F.map (homOfLE h) ≫ incl t = incl s
  /-- saturation -/
  sat : ∀ n, IsIso ((incl n).f n)

variable {C : ChainComplex (ModuleCat R) ℕ}

/-- The short complex `F_s ⟶ F_{s+1} ⟶ F_{s+1}/F_s`. -/
def sesF (ξ : Filtration R C) (s : ℕ) : ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk (incF ξ.F s) (cokernel.π (incF ξ.F s)) (cokernel.condition (incF ξ.F s))

instance (ξ : Filtration R C) (s : ℕ) : Epi (sesF ξ s).g :=
  inferInstanceAs (Epi (cokernel.π (incF ξ.F s)))

theorem sesF_shortExact (ξ : Filtration R C) (s : ℕ) : (sesF ξ s).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (incF ξ.F s)) (ξ.mono s) inferInstance

/-- `E¹_{s,t} = H_{s+t}(F_s/F_{s-1})`. -/
def E1 (ξ : Filtration R C) (s t : ℕ) : ModuleCat R :=
  (grF ξ.F s).homology (s + t)

/-- The connecting map `E¹_{s+1,t} ⟶ H_{s+t}(F_s)` (`k` of the exact couple). -/
def kF (ξ : Filtration R C) (s t : ℕ) :
    (grF ξ.F (s + 1)).homology ((s + 1) + t) ⟶ (ξ.F.obj s).homology (s + t) :=
  (sesF_shortExact ξ s).δ ((s + 1) + t) (s + t) (by simp [ComplexShape.down]; omega)

/-- The map `H_{s+t}(F_s) ⟶ E¹_{s,t}` induced by the quotient `F_s ⟶ F_s/F_{s-1}` (`j` of the
exact couple).  For `s = 0` this is the identity (`F_0/F_{-1} = F_0`). -/
def jF (ξ : Filtration R C) : (s t : ℕ) →
    (ξ.F.obj s).homology (s + t) ⟶ (grF ξ.F s).homology (s + t)
  | 0, t => 𝟙 _
  | (k + 1), t => HomologicalComplex.homologyMap (cokernel.π (incF ξ.F k)) ((k + 1) + t)

/-- The first differential `d¹ : E¹_{s+1,t} ⟶ E¹_{s,t}`. -/
def d1 (ξ : Filtration R C) (s t : ℕ) :
    (grF ξ.F (s + 1)).homology ((s + 1) + t) ⟶ (grF ξ.F s).homology (s + t) :=
  kF ξ s t ≫ jF ξ s t

/-- `d¹ ≫ d¹ = 0`: immediate from the exactness of `H(F_{s+1}) → H(F_{s+1}/F_s) → H(F_s)`. -/
theorem d1_comp_d1 (ξ : Filtration R C) (s t : ℕ) : d1 ξ (s + 1) t ≫ d1 ξ s t = 0 := by
  have hj : jF ξ (s + 1) t ≫ kF ξ s t = 0 :=
    ShortComplex.ShortExact.comp_δ (sesF_shortExact ξ s) ((s + 1) + t) (s + t)
      (by simp [ComplexShape.down]; omega)
  rw [d1, d1, Category.assoc, ← Category.assoc (jF ξ (s + 1) t), hj, zero_comp, comp_zero]

/-- The E¹ **row complex** (indexed by `s`): `... → E¹_{s+1,t} → E¹_{s,t} → ...`. -/
def E1Complex (R : Type) [CommRing R] [Nontrivial R] {C : ChainComplex (ModuleCat R) ℕ}
    (ξ : Filtration R C) (t : ℕ) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun s => E1 ξ s t) (fun s => d1 ξ s t) (fun s => d1_comp_d1 ξ s t)

/-- The E² page `E²_{s,t} = H_s(E¹_{*,t})`. -/
def E2 (ξ : Filtration R C) (s t : ℕ) : ModuleCat R :=
  (E1Complex R ξ t).homology s

/-- The image filtration `Φ_s = im(H_n(F_s) → H_n(C)) ⊆ H_n(C)`, with `Φ_s = ⊥` for `s < 0`. -/
def Phi (ξ : Filtration R C) (n : ℕ) (s : ℤ) : Submodule R (C.homology n) :=
  if s < 0 then ⊥ else (HomologicalComplex.homologyMap (ξ.incl s.toNat) n).hom.range


/-- The image filtration is increasing, as a function of the filtration index. -/
theorem Phi_mono (ξ : Filtration R C) (n : ℕ) : Monotone (Phi ξ n) := by
  intro a b hab
  simp only [Phi]
  by_cases ha : a < 0
  · rw [if_pos ha]
    exact bot_le
  · rw [if_neg ha]
    have hb : ¬ b < 0 := by omega
    rw [if_neg hb]
    have hab' : a.toNat ≤ b.toNat := by omega
    have key : ξ.incl a.toNat = ξ.F.map (homOfLE hab') ≫ ξ.incl b.toNat := (ξ.compat hab').symm
    rw [key, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]
    exact LinearMap.range_comp_le_range _ _

@[simp] theorem Phi_of_neg (ξ : Filtration R C) (n : ℕ) {s : ℤ} (h : s < 0) :
    Phi ξ n s = ⊥ := by
  simp only [Phi]
  exact dif_pos h

end

end Work.SSSR

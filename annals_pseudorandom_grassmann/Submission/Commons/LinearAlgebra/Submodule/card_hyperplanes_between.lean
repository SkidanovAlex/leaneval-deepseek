import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit

namespace Commons.LinearAlgebra.Submodule

set_option linter.style.haveILetI false

open Module

noncomputable section

/-- In `ZMod 2`, the only nonzero element is `1`. -/
lemma zmod2_eq_one_of_ne_zero (x : ZMod 2) (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl h
  · rfl

/-- Every element of `ZMod 2` is `0` or `1`. -/
lemma zmod2_eq_zero_or_eq_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Two linear functionals `M →ₗ[ZMod 2] ZMod 2` with the same kernel are equal. -/
lemma eq_of_ker_eq_ker {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {φ ψ : M →ₗ[ZMod 2] ZMod 2} (h : LinearMap.ker φ = LinearMap.ker ψ) : φ = ψ := by
  ext x
  by_cases hx : x ∈ LinearMap.ker φ
  · have hx' : x ∈ LinearMap.ker ψ := h ▸ hx
    rw [LinearMap.mem_ker] at hx hx'
    simp [hx, hx']
  · have hxψ : x ∉ LinearMap.ker ψ := by rw [← h]; exact hx
    have hxφ : φ x = 1 := zmod2_eq_one_of_ne_zero _ (by simpa [LinearMap.mem_ker] using hx)
    have hxψ1 : ψ x = 1 := zmod2_eq_one_of_ne_zero _ (by simpa [LinearMap.mem_ker] using hxψ)
    simp [hxφ, hxψ1]

/-- The kernel of a nonzero functional `M →ₗ[ZMod 2] ZMod 2` has dimension `finrank M - 1`. -/
lemma finrank_ker_eq_finrank_sub_one {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [FiniteDimensional (ZMod 2) M] {φ : M →ₗ[ZMod 2] ZMod 2} (hφ : φ ≠ 0) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker φ) = Module.finrank (ZMod 2) M - 1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  have hrange_ne_bot : LinearMap.range φ ≠ ⊥ := by
    intro hbot
    exact hφ ((LinearMap.range_eq_bot).mp hbot)
  have htop : LinearMap.range φ = ⊤ := by
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hrange_ne_bot
    have h1mem : (1 : ZMod 2) ∈ LinearMap.range φ := by
      rwa [zmod2_eq_one_of_ne_zero x hx0] at hx
    rw [Submodule.eq_top_iff']
    intro y
    rcases zmod2_eq_zero_or_eq_one y with h | h
    · rw [h]; exact Submodule.zero_mem _
    · rw [h]; exact h1mem
  have hrange_fin : Module.finrank (ZMod 2) ↥(LinearMap.range φ) = 1 := by
    rw [htop, finrank_top, Module.finrank_self]
  rw [hrange_fin] at hrn
  omega

/-- In a finite type, the number of elements different from a fixed `a` is `Nat.card α - 1`. -/
lemma natCard_subtype_ne_one {α : Type*} [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} = Nat.card α - 1 := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [show (Fintype.card {x : α // x ≠ a}) = Fintype.card {x : α // ¬ (x = a)} from rfl]
  rw [Fintype.card_subtype_compl (fun x : α => x = a), Fintype.card_subtype_eq]

/-- **Counting hyperplanes in an interval of submodules over `𝔽₂`.** Let `C ≤ L` be
submodules of a finite `𝔽₂`-vector space `V` with `finrank L = ℓ ≥ 1`. Then the number of
submodules `H` with `C ≤ H ≤ L` and `finrank H = ℓ - 1` (i.e. the hyperplanes of `L`
containing `C`) equals `2 ^ (ℓ - finrank C) - 1`.

These are exactly the nonzero linear functionals on `L` vanishing on `C` (over `𝔽₂` a
hyperplane determines, and is determined by, a unique nonzero functional): the map
`φ ↦ L.subtype '' ker φ` is a bijection, and the space of such functionals is the dual
annihilator of `C` inside `L`, of dimension `finrank L - finrank C = ℓ - finrank C`. -/
theorem card_hyperplanes_between {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (C L : Submodule (ZMod 2) V) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hCL : C ≤ L)
    (hL : Module.finrank (ZMod 2) L = ℓ) :
    Nat.card {H : Submodule (ZMod 2) V // C ≤ H ∧ H ≤ L ∧
        Module.finrank (ZMod 2) H = ℓ - 1} =
      2 ^ (ℓ - Module.finrank (ZMod 2) C) - 1 := by
  classical
  haveI hdual_fin : Finite (Module.Dual (ZMod 2) ↥L) := by
    haveI : Finite (↥L → ZMod 2) := inferInstance
    exact Finite.of_injective (fun f : Module.Dual (ZMod 2) ↥L => (f : ↥L → ZMod 2))
      (fun a b h => by ext x; exact congr_fun h x)
  set C' : Submodule (ZMod 2) ↥L := Submodule.comap L.subtype C with hC'
  set D : Submodule (ZMod 2) (Module.Dual (ZMod 2) ↥L) := Submodule.dualAnnihilator C' with hD
  let f : {φ : Module.Dual (ZMod 2) ↥L // φ ≠ 0 ∧ φ ∈ D} →
      {H : Submodule (ZMod 2) V // C ≤ H ∧ H ≤ L ∧ Module.finrank (ZMod 2) H = ℓ - 1} :=
    fun φ => ⟨Submodule.map L.subtype (LinearMap.ker φ.1),
      (fun c hc => by
        refine Submodule.mem_map.mpr ⟨⟨c, hCL hc⟩, ?_, rfl⟩
        rw [LinearMap.mem_ker]
        exact (Submodule.mem_dualAnnihilator φ.1).mp φ.2.2 ⟨c, hCL hc⟩ (by
          rw [hC', Submodule.mem_comap]; exact hc)),
      Submodule.map_subtype_le L _,
      (by
        rw [Submodule.finrank_map_subtype_eq, finrank_ker_eq_finrank_sub_one φ.2.1, hL])⟩
  have hf_inj : Function.Injective f := by
    intro φ ψ h
    apply Subtype.ext
    have hmap : Submodule.map L.subtype (LinearMap.ker φ.1) =
        Submodule.map L.subtype (LinearMap.ker ψ.1) := congrArg Subtype.val h
    exact eq_of_ker_eq_ker (Submodule.map_injective_of_injective L.subtype_injective hmap)
  have hf_surj : Function.Surjective f := by
    rintro ⟨H, hCH, hHL, hfin⟩
    let K : Submodule (ZMod 2) ↥L := Submodule.comap L.subtype H
    have hmapK : Submodule.map L.subtype K = H := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hHL]
    have hfinK : Module.finrank (ZMod 2) ↥K = ℓ - 1 := by
      rw [← Submodule.finrank_map_subtype_eq L K, hmapK, hfin]
    have hquot : Module.finrank (ZMod 2) (↥L ⧸ K) = 1 := by
      have hqn := Submodule.finrank_quotient_add_finrank K
      rw [hfinK, hL] at hqn
      omega
    let e : (↥L ⧸ K) ≃ₗ[ZMod 2] ZMod 2 :=
      LinearEquiv.ofFinrankEq _ _ (by rw [hquot, Module.finrank_self])
    let φ : Module.Dual (ZMod 2) ↥L := e.toLinearMap.comp K.mkQ
    have hkerφ : LinearMap.ker φ = K := by
      change LinearMap.ker (e.toLinearMap.comp K.mkQ) = K
      rw [LinearMap.ker_comp (K.mkQ) (e.toLinearMap), LinearMap.ker_eq_bot.mpr e.injective,
        Submodule.comap_bot, Submodule.ker_mkQ]
    have hφne : φ ≠ 0 := by
      intro h0
      obtain ⟨y, hy⟩ := K.mkQ_surjective (e.symm 1)
      have h1 : φ y = 1 := by
        change e (K.mkQ y) = 1
        rw [hy, LinearEquiv.apply_symm_apply]
      rw [h0, LinearMap.zero_apply] at h1
      exact one_ne_zero h1.symm
    have hφD : φ ∈ D := by
      rw [hD, Submodule.mem_dualAnnihilator]
      intro w hw
      have hwC : (w : V) ∈ C := Submodule.mem_comap.mp (by rwa [hC'] at hw)
      have hwH : (w : V) ∈ H := hCH hwC
      have hwK : w ∈ K := Submodule.mem_comap.mpr hwH
      rw [← hkerφ, LinearMap.mem_ker] at hwK
      exact hwK
    refine ⟨⟨φ, hφne, hφD⟩, ?_⟩
    apply Subtype.ext
    show Submodule.map L.subtype (LinearMap.ker φ) = H
    rw [hkerφ, hmapK]
  have hbij : Nat.card {φ : Module.Dual (ZMod 2) ↥L // φ ≠ 0 ∧ φ ∈ D} =
      Nat.card {H : Submodule (ZMod 2) V // C ≤ H ∧ H ≤ L ∧
        Module.finrank (ZMod 2) H = ℓ - 1} :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  rw [← hbij]
  have hDcard : Nat.card D = 2 ^ Module.finrank (ZMod 2) D := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D), Nat.card_zmod]
  have hfinD : Module.finrank (ZMod 2) D = ℓ - Module.finrank (ZMod 2) C := by
    have hfinC' : Module.finrank (ZMod 2) C' = Module.finrank (ZMod 2) C :=
      LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (p := C) (q := L) hCL)
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (K := ZMod 2) (V := ↥L) C'
    rw [← hD, hfinC', hL] at h
    omega
  have hTcard : Nat.card {φ : Module.Dual (ZMod 2) ↥L // φ ≠ 0 ∧ φ ∈ D} =
      2 ^ (ℓ - Module.finrank (ZMod 2) C) - 1 := by
    have eT : {φ : Module.Dual (ZMod 2) ↥L // φ ≠ 0 ∧ φ ∈ D} ≃
        {φ : D // (φ : Module.Dual (ZMod 2) ↥L) ≠ 0} :=
      (Equiv.subtypeEquivRight (fun φ => and_comm)).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun φ : Module.Dual (ZMod 2) ↥L => φ ∈ D)
          (fun φ => φ ≠ 0)).symm
    have hT2 : Nat.card {φ : D // (φ : Module.Dual (ZMod 2) ↥L) ≠ 0} = Nat.card D - 1 := by
      have heq : Nat.card {φ : D // (φ : Module.Dual (ZMod 2) ↥L) ≠ 0} =
          Nat.card {φ : D // φ ≠ 0} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun φ : D => by
          constructor
          · intro h h0; exact h (by rw [h0]; rfl)
          · intro h h0; exact h (Subtype.ext h0)))
      rw [heq, natCard_subtype_ne_one (0 : D)]
    calc Nat.card {φ : Module.Dual (ZMod 2) ↥L // φ ≠ 0 ∧ φ ∈ D}
        = Nat.card {φ : D // (φ : Module.Dual (ZMod 2) ↥L) ≠ 0} := Nat.card_congr eT
      _ = Nat.card D - 1 := hT2
      _ = 2 ^ Module.finrank (ZMod 2) D - 1 := by rw [hDcard]
      _ = 2 ^ (ℓ - Module.finrank (ZMod 2) C) - 1 := by rw [hfinD]
  rw [hTcard]

end

end Commons.LinearAlgebra.Submodule
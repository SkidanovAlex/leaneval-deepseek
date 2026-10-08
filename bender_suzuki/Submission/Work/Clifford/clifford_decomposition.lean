import Mathlib
import Submission.Work.Clifford.Orbit
import Submission.Work.Clifford.ResSetup
import Submission.Work.Clifford.nontrivial_resMod
import Submission.Work.Clifford.eq_top_of_forall_conjSub_le
import Submission.Work.Clifford.exists_simple_fdrep_of_submodule
import Submission.Work.Clifford.conjSub_isotypicComponent
import Submission.Work.Clifford.subChar_conjSub
import Submission.Work.Clifford.subChar_isotypicComponent
import Submission.Work.Clifford.linearEquiv_of_subChar_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open Classical
open scoped MonoidAlgebra

namespace Work.Clifford

variable {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]

/-- The supremum of a finset of elements of a complete lattice is the supremum over its
subtype. -/
theorem sSup_finset_eq_iSup_subtype {α : Type*} [CompleteLattice α] (s : Finset α) :
    sSup (↑s : Set α) = ⨆ a : ↥s, (a : α) := by
  rw [sSup_eq_iSup]
  exact (iSup_subtype (p := fun c : α => c ∈ s) (f := fun c : ↥s => (c : α))).symm

theorem clifford_decomposition {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    {χ : G → ℂ} (hχ : χ ∈ Work.Clifford.Irr G) :
    ∃ θ : N → ℂ, θ ∈ Work.Clifford.Irr N ∧
      ∃ e : ℕ, 0 < e ∧ Work.Clifford.resFun N χ = (e : ℂ) • Work.Clifford.orbitSum N θ := by
  classical
  obtain ⟨V, hVs, hVχ⟩ := mem_Irr.mp hχ
  haveI : CategoryTheory.Simple V := hVs
  haveI hNt : Nontrivial (ResMod N V) := nontrivial_resMod V
  -- a simple `ℂ[N]`-submodule of the restriction, and the irreducible `θ` it produces
  obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)
  haveI hSsimple : IsSimpleModule (MonoidAlgebra ℂ ↥N) ↥S := hS
  obtain ⟨W, hWs, hWchar⟩ := exists_simple_fdrep_of_submodule V hS
  haveI : CategoryTheory.Simple W := hWs
  have hθmem : W.character ∈ Irr N := ⟨W, hWs, rfl⟩
  -- the isotypic component of `S`, and its multiplicity `e`
  set Z : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V) :=
    isotypicComponent (MonoidAlgebra ℂ ↥N) (ResMod N V) ↥S with hZdef
  haveI hZfin : Module.Finite (MonoidAlgebra ℂ ↥N) ↥Z := moduleFinite_subtype V Z
  obtain ⟨e, E⟩ := IsIsotypicOfType.linearEquiv_fun (R := MonoidAlgebra ℂ ↥N)
    (IsIsotypicOfType.isotypicComponent (MonoidAlgebra ℂ ↥N) (ResMod N V) ↥S)
  -- `Z` is nonzero, hence `e > 0`
  have hZne : Z ≠ ⊥ := fun h => (bot_lt_iff_ne_bot.mp (bot_lt_isotypicComponent
    (R := MonoidAlgebra ℂ ↥N) (M := ResMod N V) S)) (by rw [← hZdef]; exact h)
  have he_pos : 0 < e := by
    by_contra he
    have he0 : e = 0 := Nat.eq_zero_of_not_pos he
    have hE0 : Nonempty (↥Z ≃ₗ[MonoidAlgebra ℂ ↥N] (Fin 0 → ↥S)) := he0 ▸ E
    obtain ⟨E0⟩ := hE0
    haveI : Nontrivial ↥Z := Submodule.nontrivial_iff_ne_bot.mpr hZne
    obtain ⟨z, hz⟩ := exists_ne (0 : ↥Z)
    have h1 : E0 z ≠ 0 := fun hh => hz (E0.injective (by rw [hh, map_zero]))
    exact h1 (funext fun i => Fin.elim0 i)
  -- the multiplicity identity for `Z`
  have hZmult : ∀ n : N, subChar V Z n = (e : ℂ) * subChar V S n :=
    fun n => subChar_isotypicComponent V S e ⟨E.some⟩ n
  -- `G`-orbit of the isotypic components
  set W' : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V) :=
    ⨆ g : G, conjSub V g Z with hW'def
  have hZW' : Z ≤ W' := by
    have h := le_iSup (fun g : G => conjSub V g Z) 1
    rwa [conjSub_one] at h
  have hW'ne : W' ≠ ⊥ := fun h => hZne (le_bot_iff.mp (h ▸ hZW'))
  have hstab : ∀ h : G, conjSub V h W' ≤ W' := by
    intro h
    have h1 : W' ≤ conjSub V h⁻¹ W' := iSup_le fun g => by
      have h2 := conjSub_mono V h⁻¹ (le_iSup (fun g' : G => conjSub V g' Z) (h * g))
      rw [conjSub_mul, show h⁻¹ * (h * g) = g from by group] at h2
      exact h2
    have h3 := conjSub_mono V h h1
    rwa [conjSub_mul, mul_inv_cancel, conjSub_one] at h3
  have hW'top : W' = ⊤ := eq_top_of_forall_conjSub_le V W' hW'ne hstab
  -- the finite set of isotypic components in the orbit
  set Cfin : Finset (Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)) :=
    Finset.univ.image (fun g : G => conjSub V g Z) with hCfin
  have hCfin_mem : ∀ c ∈ Cfin, c ∈ isotypicComponents (MonoidAlgebra ℂ ↥N) (ResMod N V) := by
    intro c hc
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hc
    rw [conjSub_isotypicComponent V g S]
    exact ⟨conjSub V g S, (isSimpleModule_conjSub_iff V g S).mpr hSsimple, rfl⟩
  have hCfin_sup : (⨆ c : ↥Cfin, (c : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V))) = ⊤ := by
    rw [← sSup_finset_eq_iSup_subtype]
    have h1 : (↑Cfin : Set (Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)))
        = Set.range (fun g : G => conjSub V g Z) := by
      rw [hCfin, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rw [h1, sSup_range]
    exact hW'top
  -- the trace decomposition of `V.character (n : G)`
  have htrace : ∀ n : N, V.character (n : G) = ∑ c ∈ Cfin, subChar V c n := by
    intro n
    have hf : ∀ c : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V),
        Set.MapsTo (resAct N V n) ↑(c.restrictScalars ℂ) ↑(c.restrictScalars ℂ) := by
      intro c x hx
      have h : (MonoidAlgebra.of ℂ ↥N n) • x ∈ c := c.smul_mem _ hx
      rwa [of_smul] at h
    have hind0 : iSupIndep fun c : ↥Cfin =>
        (c : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)) :=
      (sSupIndep_iff _).mp (sSupIndep.mono (sSupIndep_isotypicComponents _ _) hCfin_mem)
    have hind : iSupIndep fun c : ↥Cfin =>
        ((c : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)).restrictScalars ℂ) :=
      iSupIndep_restrictScalars V hind0
    have htop : (⨆ c : ↥Cfin,
        ((c : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)).restrictScalars ℂ)) = ⊤ := by
      rw [← Submodule.restrictScalars_iSup, ← Submodule.restrictScalars_top (S := ℂ)
        (R := MonoidAlgebra ℂ ↥N), hCfin_sup]
    have hInt : DirectSum.IsInternal fun c : ↥Cfin =>
        ((c : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)).restrictScalars ℂ) :=
      (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨hind, htop⟩
    have hmain := LinearMap.trace_eq_sum_trace_restrict (R := ℂ)
      (M := ResMod N V)
      (N := fun c : ↥Cfin => ((c : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)).restrictScalars ℂ))
      hInt (f := resAct N V n) (fun c => hf (c : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)))
    have hL : LinearMap.trace ℂ (ResMod N V) (resAct N V n) = V.character (n : G) := rfl
    have hcongr : (∑ i ∈ Cfin.attach, LinearMap.trace ℂ ↥(((i : Submodule (MonoidAlgebra ℂ ↥N)
        (ResMod N V)).restrictScalars ℂ)) (LinearMap.restrict (resAct N V n) (hf i)))
        = ∑ i ∈ Cfin.attach, subChar V (i : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)) n :=
      Finset.sum_congr rfl fun i _ => rfl
    have hconv : (∑ i : ↥Cfin, LinearMap.trace ℂ ↥(((i : Submodule (MonoidAlgebra ℂ ↥N)
        (ResMod N V)).restrictScalars ℂ)) (LinearMap.restrict (resAct N V n) (hf i)))
        = ∑ c ∈ Cfin, subChar V c n := by
      rw [Finset.univ_eq_attach, hcongr]
      exact Finset.sum_attach Cfin (fun c => subChar V c n)
    rw [← hL, hmain, hconv]
  -- the "type character" of a component, as a function of the conjugating element
  have hfiber : ∀ g h : G, conjSub V g Z = conjSub V h Z ↔
      (fun m : N => W.character (conjHomHom g m)) =
        (fun m : N => W.character (conjHomHom h m)) := by
    intro g h
    constructor
    · intro hgh
      have h1 : subChar V (conjSub V g Z) = subChar V (conjSub V h Z) := by rw [hgh]
      have h2 : ∀ m : N, subChar V Z (conjHomHom g m) = subChar V Z (conjHomHom h m) := by
        intro m
        rw [← subChar_conjSub V g Z m, ← subChar_conjSub V h Z m]
        exact congrFun h1 m
      have he : (e : ℂ) ≠ 0 := by exact_mod_cast he_pos.ne'
      have h3 : ∀ m : N, subChar V S (conjHomHom g m) = subChar V S (conjHomHom h m) := by
        intro m
        have h4 : (e : ℂ) * subChar V S (conjHomHom g m) =
            (e : ℂ) * subChar V S (conjHomHom h m) := by
          rw [← hZmult (conjHomHom g m), ← hZmult (conjHomHom h m)]
          exact h2 m
        rcases mul_eq_mul_left_iff.mp h4 with hh | hh
        · exact hh
        · exact absurd hh he
      funext m
      rw [hWchar (conjHomHom g m), hWchar (conjHomHom h m)]
      exact h3 m
    · intro hgh
      have h1 : subChar V (conjSub V g S) = subChar V (conjSub V h S) := by
        funext m
        rw [subChar_conjSub V g S m, subChar_conjSub V h S m,
          ← hWchar (conjHomHom g m), ← hWchar (conjHomHom h m)]
        exact congrFun hgh m
      haveI : IsSimpleModule (MonoidAlgebra ℂ ↥N) ↥(conjSub V g S) :=
        (isSimpleModule_conjSub_iff V g S).mpr hSsimple
      haveI : IsSimpleModule (MonoidAlgebra ℂ ↥N) ↥(conjSub V h S) :=
        (isSimpleModule_conjSub_iff V h S).mpr hSsimple
      obtain ⟨E1⟩ := linearEquiv_of_subChar_eq V (conjSub V g S) (conjSub V h S) h1
      rw [hZdef, conjSub_isotypicComponent V g S, conjSub_isotypicComponent V h S,
        LinearEquiv.isotypicComponent_eq E1]
  let typeChar : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V) → N → ℂ :=
    fun c => if h : ∃ g : G, conjSub V g Z = c then
      fun m => W.character (conjHomHom h.choose m) else 0
  have htypeChar : ∀ g : G, typeChar (conjSub V g Z) =
      fun m : N => W.character (conjHomHom g m) := by
    intro g
    have h : ∃ g' : G, conjSub V g' Z = conjSub V g Z := ⟨g, rfl⟩
    simp only [typeChar]
    rw [dite_eq_left h]
    exact (hfiber h.choose g).mp h.choose_spec
  have htypeChar_inj : Set.InjOn typeChar ↑Cfin := by
    intro c hc c' hc' hcc
    rw [Finset.mem_coe] at hc hc'
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨g', -, rfl⟩ := Finset.mem_image.mp hc'
    rw [htypeChar, htypeChar] at hcc
    exact (hfiber g g').mpr hcc
  have hPsi (g : G) : (fun m : N => W.character (conjHomHom g m)) =
      conjFun N g⁻¹ W.character := by
    funext m
    show W.character (conjHomHom g m) = W.character ⟨g⁻¹ * (m : G) * (g⁻¹)⁻¹, _⟩
    congr 1
    exact Subtype.ext (by simp only [conjHomHom_apply]; group)
  have himage : Cfin.image typeChar = charOrbit N W.character := by
    rw [hCfin, Finset.image_image]
    have h1 : (typeChar ∘ fun g : G => conjSub V g Z) =
        fun g : G => fun m : N => W.character (conjHomHom g m) := by
      funext g
      exact htypeChar g
    rw [h1]
    have h2 : (fun g : G => fun m : N => W.character (conjHomHom g m)) =
        fun g : G => conjFun N g⁻¹ W.character := by
      funext g
      exact hPsi g
    rw [h2, charOrbit]
    ext φ
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp only [inv_inv]⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp only [inv_inv]⟩
  have hsum_types : ∀ n : N, (∑ c ∈ Cfin, typeChar c n) = orbitSum N W.character n := by
    intro n
    rw [← Finset.sum_image (f := fun ψ : N → ℂ => ψ n) htypeChar_inj, himage]
    rfl
  -- conclusion
  refine ⟨W.character, hθmem, e, he_pos, ?_⟩
  ext n
  have hcomp : ∀ c ∈ Cfin, subChar V c n = (e : ℂ) * typeChar c n := by
    intro c hc
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hc
    rw [htypeChar g]
    show subChar V (conjSub V g Z) n = (e : ℂ) * W.character (conjHomHom g n)
    rw [subChar_conjSub V g Z n, hZmult (conjHomHom g n), ← hWchar (conjHomHom g n)]
  rw [resFun_apply, Pi.smul_apply, smul_eq_mul, ← hVχ, htrace n,
    Finset.sum_congr rfl hcomp, ← Finset.mul_sum]
  congr 1
  exact hsum_types n

end Work.Clifford

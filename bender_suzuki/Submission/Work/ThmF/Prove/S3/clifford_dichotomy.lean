import Submission.Work.ThmF.Prove.S3.clifford_setup
import Submission.Work.ThmF.Prove.S3.conjModBase
import Submission.Work.ThmF.Prove.S3.conjMod_mem_isotypicComponents
import Submission.Work.ThmF.Prove.S3.isotypicComponentsFinite
import Submission.Work.ThmF.Prove.S3.finrank_eq_sum_isotypicComponents

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option backward.isDefEq.respectTransparency false

noncomputable section

set_option linter.unusedSectionVars false

open scoped MonoidAlgebra
open Classical

namespace Work.ThmF.Prove.S3

/-- Restricting scalars along a compatible action preserves the property of a submodule being
nonzero. -/
theorem restrictScalars_ne_bot_iff {S R M : Type*} [Semiring R] [AddCommMonoid M]
    [Semiring S] [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]
    {N : Submodule R M} : N.restrictScalars S ≠ ⊥ ↔ N ≠ ⊥ := by
  constructor
  · intro h hN
    exact h (by rw [hN, Submodule.restrictScalars_bot])
  · intro h hb
    exact h (le_bot_iff.mp fun x hx => by
      have h1 : x ∈ N.restrictScalars S := (Submodule.restrictScalars_mem S N x).mpr hx
      rw [hb] at h1
      exact h1)

/-- Restricting scalars along a compatible action preserves the property of a submodule being
zero. -/
theorem restrictScalars_eq_bot_iff {S R M : Type*} [Semiring R] [AddCommMonoid M]
    [Semiring S] [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]
    {N : Submodule R M} : N.restrictScalars S = ⊥ ↔ N = ⊥ := by
  constructor
  · intro h
    exact le_bot_iff.mp fun x hx => by
      have h1 : x ∈ N.restrictScalars S := (Submodule.restrictScalars_mem S N x).mpr hx
      rw [h] at h1
      exact h1
  · intro h
    rw [h, Submodule.restrictScalars_bot]

/-- **Clifford dichotomy.**  Let `L` be a finite group, `K ⊴ L`, `E ≤ L` of prime order `p` with
`K ⊓ E = ⊥`, `K ⊔ E = ⊤`, and `V` an irreducible `F[L]`-module of dimension `p` over a field `F`
whose characteristic does not divide `|K|`.  Then `V`, as an `F[K]`-module, either has a
one-dimensional submodule or is irreducible. -/
theorem clifford_dichotomy {L : Type*} [Group L] [Fintype L] {F : Type*} [Field F]
    {K E : Subgroup L} (hKn : K.Normal) (hinf : K ⊓ E = ⊥) (hsup : K ⊔ E = ⊤)
    {p : ℕ} (hp : p.Prime) (hEcard : Nat.card ↥E = p)
    (hchar : ∀ q : ℕ, q.Prime → (q : F) = 0 → ¬ q ∣ Nat.card ↥K)
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hV : Module.finrank F V = p) (ρ : Representation F L V)
    (hirr : ∀ W : Submodule F V, (∀ l : L, ∀ w ∈ W, ρ l w ∈ W) → W ≠ ⊥ → W = ⊤) :
    (∃ U : Submodule F V, U ≠ ⊥ ∧ (∀ k ∈ K, ∀ u ∈ U, ρ k u ∈ U) ∧ Module.finrank F U = 1) ∨
    (∀ W : Submodule F V, (∀ k ∈ K, ∀ w ∈ W, ρ k w ∈ W) → W ≠ ⊥ → W = ⊤) := by
  classical
  haveI hne : NeZero (Nat.card ↥K : F) :=
    neZero_natCast_of_char (Nat.card_pos (α := ↥K)).ne' hchar
  by_cases hP : ∃ U : Submodule F V, U ≠ ⊥ ∧ (∀ k ∈ K, ∀ u ∈ U, ρ k u ∈ U) ∧
      Module.finrank F U = 1
  · exact Or.inl hP
  · refine Or.inr ?_
    simp only [not_exists, not_and] at hP
    intro W hW hWne
    haveI hss : IsSemisimpleModule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule :=
      inferInstance
    haveI hfinm : Module.Finite (MonoidAlgebra F K) (resRep (K := K) ρ).asModule :=
      Module.Finite.of_restrictScalars_finite F (MonoidAlgebra F K) (resRep (K := K) ρ).asModule
    have hfdim : 0 < Module.finrank F V := by rw [hV]; exact hp.pos
    haveI hntV : Nontrivial V := Module.nontrivial_of_finrank_pos hfdim
    haveI hntM : Nontrivial (resRep (K := K) ρ).asModule := hntV
    -- a simple `F[K]`-submodule
    obtain ⟨S₀, -, hS₀s⟩ :=
      (IsSemisimpleModule.eq_bot_or_exists_simple_le (⊤ : Submodule (MonoidAlgebra F K)
        (resRep (K := K) ρ).asModule)).resolve_left
        (bot_lt_top.ne' : (⊤ : Submodule (MonoidAlgebra F K)
          (resRep (K := K) ρ).asModule) ≠ ⊥)
    set C₀ : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule :=
      isotypicComponent (MonoidAlgebra F K) (resRep (K := K) ρ).asModule S₀ with hC₀def
    have hC₀mem : C₀ ∈ isotypicComponents (MonoidAlgebra F K) (resRep (K := K) ρ).asModule :=
      ⟨S₀, hS₀s, rfl⟩
    have hΞfin : (isotypicComponents (MonoidAlgebra F K)
        (resRep (K := K) ρ).asModule).Finite := isotypicComponentsFinite ρ
    haveI hΞfty : Fintype (isotypicComponents (MonoidAlgebra F K)
        (resRep (K := K) ρ).asModule) := hΞfin.fintype
    -- the orbit of `C₀` under `E`
    set Orb : Set (Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule) :=
      Set.range (fun e : ↥E => conjMod hKn ρ (e : L) C₀) with hOrbdef
    have hOrb_sub : Orb ⊆ isotypicComponents (MonoidAlgebra F K)
        (resRep (K := K) ρ).asModule := by
      rintro _ ⟨e, rfl⟩
      exact conjMod_mem_isotypicComponents hKn ρ (e : L) hC₀mem
    have hC₀ne : C₀ ≠ ⊥ := (bot_lt_isotypicComponent S₀).ne'
    have hOrb_stable : ∀ e : ↥E, conjMod hKn ρ (e : L) '' Orb = Orb := by
      intro e
      ext X
      constructor
      · rintro ⟨Y, ⟨f, rfl⟩, rfl⟩
        refine ⟨e * f, ?_⟩
        show conjMod hKn ρ (((e * f : ↥E) : L)) C₀ =
          conjMod hKn ρ ((e : L)) (conjMod hKn ρ ((f : L)) C₀)
        rw [Subgroup.coe_mul, ← conjMod_mul]
      · rintro ⟨f, rfl⟩
        refine ⟨conjMod hKn ρ (((e⁻¹ * f : ↥E) : L)) C₀, ⟨e⁻¹ * f, rfl⟩, ?_⟩
        show conjMod hKn ρ ((e : L)) (conjMod hKn ρ (((e⁻¹ * f : ↥E) : L)) C₀) =
          conjMod hKn ρ ((f : L)) C₀
        rw [conjMod_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        congr 1
        group
    have hsSup_stable : ∀ e : ↥E, conjMod hKn ρ (e : L) (sSup Orb) = sSup Orb := by
      intro e
      rw [conjMod_sSup, hOrb_stable]
    -- `sSup Orb` is `L`-invariant
    have hLinv : ∀ l : L, ∀ w ∈ (Subrepresentation.ofSubmodule' (sSup Orb)).toSubmodule,
        ρ l w ∈ (Subrepresentation.ofSubmodule' (sSup Orb)).toSubmodule := by
      set W' : Submodule F V := (Subrepresentation.ofSubmodule' (sSup Orb)).toSubmodule with hW'def
      have hone : ∀ x : V, ρ (1 : L) x = x := fun x => act_one (K := K) ρ x
      have honeinv : ∀ x : V, ρ ((1 : L)⁻¹) x = x := fun x => by
        have h := act_one (K := K) ρ x
        simpa using h
      have hmul : ∀ (a b : L) (x : V), ρ a (ρ b x) = ρ (a * b) x :=
        fun a b x => act_mul_apply (K := K) ρ a b x
      have hcompinv : ∀ (a : L) (x : V), ρ a (ρ (a⁻¹) x) = x :=
        fun a x => act_comp_inv (K := K) ρ a x
      have hmem_of_eq : ∀ (l : L), W'.map (ρ l) = W' → ∀ w ∈ W', ρ l w ∈ W' := by
        intro l hl w hw
        have h1 : ρ l w ∈ W'.map (ρ l) := Submodule.mem_map.mpr ⟨w, hw, rfl⟩
        rwa [hl] at h1
      have hKInv : ∀ (k : ↥K), ∀ w ∈ W', ρ ((k : L)) w ∈ W' :=
        fun k w hw => (Subrepresentation.ofSubmodule' (sSup Orb)).apply_mem_toSubmodule k hw
      have hEmap : ∀ e : ↥E, W'.map (ρ ((e : L))) = W' := by
        intro e
        have h := conjMod_restrictScalars hKn ρ (e : L) (sSup Orb)
        rw [hsSup_stable e] at h
        exact h.symm
      let S : Subgroup L :=
        { carrier := {l : L | (∀ x ∈ W', ρ l x ∈ W') ∧ (∀ x ∈ W', ρ (l⁻¹) x ∈ W')}
          one_mem' := ⟨fun x hx => by rw [hone]; exact hx,
            fun x hx => by rw [honeinv]; exact hx⟩
          mul_mem' := by
            intro a b ha hb
            obtain ⟨ha1, ha2⟩ := ha
            obtain ⟨hb1, hb2⟩ := hb
            refine ⟨fun x hx => ?_, fun x hx => ?_⟩
            · have h1 : ρ b x ∈ W' := hb1 x hx
              have h2 : ρ a (ρ b x) ∈ W' := ha1 _ h1
              rw [hmul] at h2
              exact h2
            · have h1 : ρ (a⁻¹) x ∈ W' := ha2 x hx
              have h2 : ρ (b⁻¹) (ρ (a⁻¹) x) ∈ W' := hb2 _ h1
              rw [hmul (b⁻¹) (a⁻¹)] at h2
              rwa [mul_inv_rev]
          inv_mem' := by
            intro a ha
            obtain ⟨ha1, ha2⟩ := ha
            exact ⟨ha2, fun x hx => by
              have h := ha1 x hx
              simpa using h⟩ }
      have hKS : K ≤ S := by
        intro k hk
        exact ⟨fun x hx => hKInv ⟨k, hk⟩ x hx,
          fun x hx => hKInv ⟨k⁻¹, K.inv_mem hk⟩ x hx⟩
      have hES : E ≤ S := by
        intro e he
        refine ⟨fun x hx => hmem_of_eq e (hEmap ⟨e, he⟩) x hx, fun x hx => ?_⟩
        have h1 : W'.map (ρ (e⁻¹)) = W' := by
          have h2 := hEmap (⟨e, he⟩ : ↥E)⁻¹
          simpa only [Subgroup.coe_inv] using h2
        exact hmem_of_eq _ h1 x hx
      have hStop : S = ⊤ := top_unique (hsup ▸ sup_le hKS hES)
      intro l w hw
      have hl : W'.map (ρ l) = W' := by
        have hmem : l ∈ S := hStop.symm ▸ Subgroup.mem_top l
        obtain ⟨h1, h2⟩ := hmem
        refine le_antisymm ?_ ?_
        · intro x hx
          obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
          rw [← hyx]
          exact h1 y hy
        · intro x hx
          refine Submodule.mem_map.mpr ⟨ρ (l⁻¹) x, h2 x hx, ?_⟩
          exact hcompinv l x
      exact hmem_of_eq l hl w hw
    have hWne' : (Subrepresentation.ofSubmodule' (sSup Orb)).toSubmodule ≠ ⊥ := by
      intro hb
      have hC₀le : C₀ ≤ sSup Orb := le_sSup ⟨1, by simp⟩
      have h1 : C₀.restrictScalars F ≤
          (Subrepresentation.ofSubmodule' (sSup Orb)).toSubmodule := by
        rw [ofSubmodule'_toSubmodule]
        exact Submodule.restrictScalars_mono F hC₀le
      rw [hb] at h1
      have h2 : C₀.restrictScalars F = ⊥ := le_bot_iff.mp h1
      exact hC₀ne (restrictScalars_eq_bot_iff.mp h2)
    have hsSup_top : sSup Orb = ⊤ := by
      have hthis := hirr _ hLinv hWne'
      have h2 : (sSup Orb).restrictScalars F = (⊤ : Submodule F V) := by
        rw [← ofSubmodule'_toSubmodule (K := K) ρ (sSup Orb)]
        exact hthis
      exact (Submodule.restrictScalars_inj (S := F) (R := MonoidAlgebra F K)
        (M := (resRep (K := K) ρ).asModule) (V₁ := sSup Orb)
        (V₂ := (⊤ : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule))).mp h2
    have hOrb_eq : Orb = isotypicComponents (MonoidAlgebra F K)
        (resRep (K := K) ρ).asModule := by
      refine Set.Subset.antisymm hOrb_sub ?_
      intro C hC
      by_contra hnot
      obtain ⟨S, hS, rfl⟩ := hC
      have hdisj : Disjoint (isotypicComponent (MonoidAlgebra F K)
          (resRep (K := K) ρ).asModule S) (sSup Orb) :=
        (sSupIndep_isotypicComponents (MonoidAlgebra F K)
          (resRep (K := K) ρ).asModule).disjoint_sSup (show _ ∈
            isotypicComponents (MonoidAlgebra F K) (resRep (K := K) ρ).asModule from
              ⟨S, hS, rfl⟩)
          hOrb_sub hnot
      rw [hsSup_top, disjoint_top] at hdisj
      exact (bot_lt_isotypicComponent S).ne' hdisj
    have hconst : ∀ C ∈ isotypicComponents (MonoidAlgebra F K) (resRep (K := K) ρ).asModule,
        Module.finrank F ↥C = Module.finrank F ↥C₀ := by
      intro C hC
      have hCOrb : C ∈ Orb := hOrb_eq ▸ hC
      obtain ⟨e, he⟩ := hCOrb
      rw [← he]
      exact finrank_conjMod_eq hKn ρ (e : L) C₀
    have hdimsum : Module.finrank F V = ∑ C : (isotypicComponents (MonoidAlgebra F K)
        (resRep (K := K) ρ).asModule), Module.finrank F ↥(C : Submodule (MonoidAlgebra F K)
          (resRep (K := K) ρ).asModule) := finrank_eq_sum_isotypicComponents (K := K) ρ
    -- `p = |Ξ| · d`
    have hp_eq : p = Fintype.card (isotypicComponents (MonoidAlgebra F K)
        (resRep (K := K) ρ).asModule) * Module.finrank F ↥C₀ := by
      rw [← hV, hdimsum, Finset.sum_congr rfl (fun C _ => hconst C.1 C.2), Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      rfl
    -- `d ≥ 2`
    have hd2 : 2 ≤ Module.finrank F ↥C₀ := by
      by_contra h
      push_neg at h
      haveI hfinC : Module.Finite F ↥C₀ :=
        Submodule.finiteDimensional_of_le (S₁ := C₀.restrictScalars F) (S₂ := ⊤) le_top
      have hd1 : Module.finrank F ↥C₀ = 1 := by
        have hpos : 0 < Module.finrank F ↥C₀ :=
          (Module.finrank_pos_iff_of_free F ↥C₀).mpr (C₀.nontrivial_iff_ne_bot.mpr hC₀ne)
        omega
      have hne : (Subrepresentation.ofSubmodule' C₀).toSubmodule ≠ ⊥ := by
        rw [ofSubmodule'_toSubmodule]
        exact restrictScalars_ne_bot_iff.mpr hC₀ne
      have hfr1 : Module.finrank F ↥(Subrepresentation.ofSubmodule' C₀).toSubmodule = 1 := by
        rw [ofSubmodule'_toSubmodule]
        exact hd1
      exact hP _ hne
        (fun k hk v hv => (Subrepresentation.ofSubmodule' C₀).apply_mem_toSubmodule
          ⟨k, hk⟩ hv)
        hfr1
    have hcard_one : Fintype.card (isotypicComponents (MonoidAlgebra F K)
        (resRep (K := K) ρ).asModule) = 1 := by
      rcases hp.eq_one_or_self_of_dvd _ ⟨_, hp_eq⟩ with h | h
      · exact h
      · rw [h] at hp_eq
        have hd1 : Module.finrank F ↥C₀ = 1 :=
          (Nat.eq_of_mul_eq_mul_left hp.pos (by rw [mul_one]; exact hp_eq)).symm
        omega
    -- hence a single isotypic component, namely everything
    have hsub : Subsingleton (isotypicComponents (MonoidAlgebra F K)
        (resRep (K := K) ρ).asModule) :=
      Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hcard_one)
    have hC₀top : C₀ = ⊤ := by
      have h1 : (isotypicComponents (MonoidAlgebra F K) (resRep (K := K) ρ).asModule) =
          {C₀} := by
        refine Set.eq_singleton_iff_unique_mem.mpr ⟨hC₀mem, fun D hD => ?_⟩
        exact congrArg Subtype.val (Subsingleton.elim (⟨D, hD⟩ : isotypicComponents
          (MonoidAlgebra F K) (resRep (K := K) ρ).asModule) ⟨C₀, hC₀mem⟩)
      have hΞtop : sSup (isotypicComponents (MonoidAlgebra F K) (resRep (K := K) ρ).asModule)
          = ⊤ := sSup_isotypicComponents _ _
      rw [h1, sSup_singleton] at hΞtop
      exact hΞtop
    -- consequently `V` is an isotypic `F[K]`-module
    have hiso : IsIsotypic (MonoidAlgebra F K) (resRep (K := K) ρ).asModule := by
      have htop : (⊤ : Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule) ∈
          isotypicComponents (MonoidAlgebra F K) (resRep (K := K) ρ).asModule := by
        rw [← hC₀top]; exact hC₀mem
      exact (LinearEquiv.isIsotypic_iff (Submodule.topEquiv)).mp
        (IsIsotypic.isotypicComponents htop)
    obtain ⟨n, hn, S, hSs, ⟨e⟩⟩ := hiso.linearEquiv_fun
    -- dimension count: `p = n * finrank S`
    have hSne : S ≠ ⊥ :=
      S.nontrivial_iff_ne_bot.mp (IsSimpleModule.nontrivial (MonoidAlgebra F K) ↥S)
    have hdS : 2 ≤ Module.finrank F ↥S := by
      by_contra h
      push_neg at h
      haveI hfinS : Module.Finite F ↥S :=
        Submodule.finiteDimensional_of_le (S₁ := S.restrictScalars F) (S₂ := ⊤) le_top
      have hdS1 : Module.finrank F ↥S = 1 := by
        have hpos : 0 < Module.finrank F ↥S :=
          (Module.finrank_pos_iff_of_free F ↥S).mpr (S.nontrivial_iff_ne_bot.mpr hSne)
        omega
      have hne : (Subrepresentation.ofSubmodule' S).toSubmodule ≠ ⊥ := by
        rw [ofSubmodule'_toSubmodule]
        exact restrictScalars_ne_bot_iff.mpr hSne
      have hfr1 : Module.finrank F ↥(Subrepresentation.ofSubmodule' S).toSubmodule = 1 := by
        rw [ofSubmodule'_toSubmodule]
        exact hdS1
      exact hP _ hne
        (fun k hk v hv => (Subrepresentation.ofSubmodule' S).apply_mem_toSubmodule
          ⟨k, hk⟩ hv)
        hfr1
    have hfr : Module.finrank F V = n * Module.finrank F ↥S := by
      haveI hfinS : Module.Finite F ↥S :=
        Submodule.finiteDimensional_of_le (S₁ := S.restrictScalars F) (S₂ := ⊤) le_top
      have eF : (resRep (K := K) ρ).asModule ≃ₗ[F] (Fin n → ↥S) :=
        LinearEquiv.restrictScalars F e
      have h1 : Module.finrank F ((resRep (K := K) ρ).asModule) =
          Module.finrank F (Fin n → ↥S) := LinearEquiv.finrank_eq eF
      rw [Module.finrank_pi_fintype F (M := fun _ : Fin n => ↥S), Finset.sum_const,
        Finset.card_fin, nsmul_eq_mul] at h1
      exact h1
    have hn1 : n = 1 := by
      rw [hV] at hfr
      rcases hp.eq_one_or_self_of_dvd _ ⟨_, hfr⟩ with h | h
      · exact h
      · rw [h] at hfr
        have hd1 : Module.finrank F ↥S = 1 :=
          (Nat.eq_of_mul_eq_mul_left hp.pos (by rw [mul_one]; exact hfr)).symm
        omega
    have hsimple : IsSimpleModule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule := by
      rw [hn1] at e
      have e1 : (resRep (K := K) ρ).asModule ≃ₗ[MonoidAlgebra F K] ↥S :=
        e.trans (LinearEquiv.piUnique (MonoidAlgebra F K) (fun _ : Fin 1 => ↥S))
      exact IsSimpleModule.congr e1
    -- translate to `W`
    let σ : Subrepresentation (resRep (K := K) ρ) :=
      { toSubmodule := W
        apply_mem_toSubmodule := fun k v hv => hW k k.2 v hv }
    have hasSub : (Subrepresentation.asSubmodule σ).restrictScalars F = σ.toSubmodule :=
      Submodule.ext fun _ => Iff.rfl
    have hNbot : Subrepresentation.asSubmodule σ ≠ (⊥ : Submodule (MonoidAlgebra F K)
        (resRep (K := K) ρ).asModule) := by
      intro hh
      apply hWne
      have h1 : (Subrepresentation.asSubmodule σ).restrictScalars F = (⊥ : Submodule F V) := by
        rw [hh, Submodule.restrictScalars_bot]
      rw [hasSub] at h1
      exact h1
    have hNtop : Subrepresentation.asSubmodule σ = ⊤ :=
      ((isSimpleModule_iff (MonoidAlgebra F K)
        ((resRep (K := K) ρ).asModule)).mp hsimple).eq_bot_or_eq_top _ |>.resolve_left hNbot
    have h4 : (⊤ : Submodule F V) = (Subrepresentation.asSubmodule σ).restrictScalars F := by
      rw [hNtop]
      exact (Submodule.restrictScalars_top F (MonoidAlgebra F K)
        ((resRep (K := K) ρ).asModule)).symm
    exact hasSub.symm.trans h4.symm

end Work.ThmF.Prove.S3

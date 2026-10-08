import Mathlib
import Submission.Work.CharPrelim.modular_frobenius_aux
import Submission.Work.CharPrelim.relIndex_le_finrank_invariants_of_iSupIndep_permuted

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharPrelim.finrank_invariants_ge_of_irreducible`

The modular form of Feit--Thompson 3.16 (iii) in its fixed-point dimension form, over an
arbitrary algebraically closed field `L` of prime characteristic `p` (in particular the
ZMod p case follows by base change).

Setup: `G = K ⋊ E` is a Frobenius group (`K ⊴ G`, `K ⊓ E = ⊥`, `K ⊔ E = ⊤`,
`C_G(k) ≤ K` for `1 ≠ k ∈ K`), `p ∤ |G|`, `V` is an irreducible `L`-representation of `G`
with `K ⊄ ker ρ`, and `E₀ ≤ E`.

Conclusion: `dim V^{E₀} ≥ [E : E₀]`.

Proof route: `V^K = 0`; choose a nonzero `K`-simple `K`-stable submodule `U ≤ V` (descent on
the dimension); the `E`-conjugates `W_h := ρ h • U` (`h ∈ E`) are pairwise non-isomorphic as
`K`-modules -- a `K`-equivariant isomorphism `W_g ≅ W_h` (`g ≠ h`) would give a fixed-point-free
semilinear bijection `U → U`, contradicting the modular form of FT 3.16 (iii)
(`Work.CharPrelim.no_isFixedPointFree_semilinear_bijective`).  Hence the `W_h` are independent
(`iSupIndep`), so they span `V`, and `E` permutes them freely; the orbit sums over a transversal
of `E₀ ≤ E` produce `[E : E₀]` linearly independent `E₀`-fixed vectors.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 400000

noncomputable section

open Classical
open scoped Pointwise

namespace Work.CharPrelim

variable {L : Type*} [Field L] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module L V]

/-- `U` is stable under the action of the subgroup `S`. -/
def IsStableUnder (ρ : Representation L G V) (S : Subgroup G) (U : Submodule L V) : Prop :=
  ∀ s : S, U ≤ U.comap (ρ (s : G))

section Basic

variable (ρ : Representation L G V)

lemma rho_inv_rho (h : G) (v : V) : ρ h⁻¹ (ρ h v) = v := by
  show (ρ h⁻¹ * ρ h) v = v
  rw [← map_mul, inv_mul_cancel, map_one]; rfl

lemma rho_rho_inv (h : G) (v : V) : ρ h (ρ h⁻¹ v) = v := by
  show (ρ h * ρ h⁻¹) v = v
  rw [← map_mul, mul_inv_cancel, map_one]; rfl

lemma mul_apply_eq (h g : G) (v : V) : ρ h (ρ g v) = ρ (h * g) v := by
  rw [← Module.End.mul_apply, ← map_mul]

lemma map_rho_inv_map_rho (h : G) (W : Submodule L V) :
    Submodule.map (ρ h⁻¹) (Submodule.map (ρ h) W) = W := by
  rw [← Submodule.map_comp]
  rw [show (ρ h⁻¹).comp (ρ h) = LinearMap.id from by ext v; exact rho_inv_rho ρ h v]
  exact Submodule.map_id W

lemma map_rho_map_rho_inv (h : G) (W : Submodule L V) :
    Submodule.map (ρ h) (Submodule.map (ρ h⁻¹) W) = W := by
  rw [← Submodule.map_comp]
  rw [show (ρ h).comp (ρ h⁻¹) = LinearMap.id from by ext v; exact rho_rho_inv ρ h v]
  exact Submodule.map_id W

lemma map_rho_stable {K : Subgroup G} (hKn : K.Normal) {U : Submodule L V}
    (hstab : IsStableUnder ρ K U) (h : G) :
    IsStableUnder ρ K (Submodule.map (ρ h) U) := by
  intro k x hx
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
  rw [Submodule.mem_comap]
  have hkey : ρ (k : G) * ρ h = ρ h * ρ (h⁻¹ * (k : G) * h) := by
    rw [← map_mul, ← map_mul]; congr 1; group
  rw [← Module.End.mul_apply, hkey, Module.End.mul_apply]
  exact Submodule.mem_map_of_mem (hstab ⟨h⁻¹ * (k : G) * h, hKn.conj_mem' (k : G) k.2 h⟩ hu)

lemma map_rho_simple {K : Subgroup G} (hKn : K.Normal) {U : Submodule L V} (hU : U ≠ ⊥)
    (hstab : IsStableUnder ρ K U)
    (hsimp : ∀ W : Submodule L V, W ≤ U → IsStableUnder ρ K W → W ≠ ⊥ → W = U) (h : G) :
    ∀ W : Submodule L V, W ≤ Submodule.map (ρ h) U → IsStableUnder ρ K W → W ≠ ⊥ →
      W = Submodule.map (ρ h) U := by
  intro W hW hWstab hWne
  have hWmap : Submodule.map (ρ h⁻¹) W ≤ U := by
    refine le_trans (Submodule.map_mono hW) ?_
    rw [map_rho_inv_map_rho ρ h U]
  have hWstab' : IsStableUnder ρ K (Submodule.map (ρ h⁻¹) W) :=
    map_rho_stable ρ hKn hWstab h⁻¹
  have hWne' : Submodule.map (ρ h⁻¹) W ≠ ⊥ := by
    intro hbot
    apply hWne
    have h1 : W = Submodule.map (ρ h) (Submodule.map (ρ h⁻¹) W) :=
      (map_rho_map_rho_inv ρ h W).symm
    rw [h1, hbot, Submodule.map_bot]
  have hUl : Submodule.map (ρ h⁻¹) W = U := hsimp _ hWmap hWstab' hWne'
  rw [← hUl, map_rho_map_rho_inv ρ h W]

lemma comap_bot_stable {K : Subgroup G} {f : V →ₗ[L] V}
    (hfK : ∀ k : ↥K, f.comp (ρ (k : G)) = (ρ (k : G)).comp f) :
    IsStableUnder ρ K (Submodule.comap f ⊥) := by
  intro k x hx
  simp only [Submodule.mem_comap, Submodule.mem_bot] at hx ⊢
  have h2 := congrArg (fun g : V →ₗ[L] V => g x) (hfK k)
  simp only [LinearMap.comp_apply] at h2
  rw [h2, hx, map_zero]

lemma inf_stable {K : Subgroup G} {A B : Submodule L V} (hA : IsStableUnder ρ K A)
    (hB : IsStableUnder ρ K B) : IsStableUnder ρ K (A ⊓ B) := by
  intro k x hx
  obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
  exact Submodule.mem_inf.mpr ⟨hA k hx1, hB k hx2⟩

end Basic

section Core

variable (ρ : Representation L G V) [ρ.IsIrreducible]

/-- If `K ⊴ G` and `K` is not contained in the kernel of an irreducible `ρ`, then the
`K`-invariants of `ρ` are trivial. -/
lemma invariants_comp_subtype_eq_bot {K : Subgroup G} (hKn : K.Normal)
    (hker : ¬ K ≤ ρ.ker) :
    Representation.invariants (ρ.comp K.subtype) = ⊥ := by
  classical
  by_contra hne
  haveI : K.Normal := hKn
  let W : Subrepresentation ρ :=
    ⟨Representation.invariants (ρ.comp K.subtype),
      fun g v hv => Representation.le_comap_invariants ρ K g hv⟩
  rcases eq_bot_or_eq_top W with h | h
  · exact hne (congrArg Subrepresentation.toSubmodule h)
  · exfalso
    apply hker
    intro k hk
    rw [MonoidHom.mem_ker]
    ext v
    have hv : v ∈ (W : Subrepresentation ρ) := by rw [h]; trivial
    exact hv ⟨k, hk⟩

/-- The `K`-representation on a nonzero `K`-simple `K`-stable submodule, transported to a
subrepresentation of `ρ|_K`, is irreducible. -/
lemma subrepresentation_isIrreducible {K : Subgroup G} {U : Submodule L V} (hU : U ≠ ⊥)
    (hstab : IsStableUnder ρ K U)
    (hsimp : ∀ W : Submodule L V, W ≤ U → IsStableUnder ρ K W → W ≠ ⊥ → W = U) :
    (Representation.subrepresentation (ρ.comp K.subtype) U hstab).IsIrreducible := by
  classical
  set ρU := Representation.subrepresentation (ρ.comp K.subtype) U hstab
  haveI hUnt : Nontrivial ↥U := Submodule.nontrivial_iff_ne_bot.mpr hU
  haveI : Nontrivial (Subrepresentation ρU) :=
    ⟨⊥, ⊤, by
      intro h
      have h2 : (⊥ : Submodule L ↥U) = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact absurd h2 (by simp)⟩
  refine IsSimpleOrder.mk fun A => ?_
  have hle : A.toSubmodule.map U.subtype ≤ U := Submodule.map_subtype_le U A.toSubmodule
  have hstabW : IsStableUnder ρ K (A.toSubmodule.map U.subtype) := by
    intro k x hx
    rw [Submodule.mem_comap]
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    exact Submodule.mem_map.mpr ⟨ρU k u, A.apply_mem_toSubmodule k hu, by
      simp [ρU, Representation.subrepresentation, LinearMap.restrict_apply]⟩
  by_cases hW : A.toSubmodule.map U.subtype = ⊥
  · left
    have hA : A.toSubmodule = ⊥ :=
      Submodule.map_injective_of_injective U.subtype_injective (by simp [hW])
    exact Subrepresentation.toSubmodule_injective (by rw [hA]; rfl)
  · right
    have hWU : A.toSubmodule.map U.subtype = U := hsimp _ hle hstabW hW
    have hA : A.toSubmodule = ⊤ :=
      Submodule.map_injective_of_injective U.subtype_injective
        (by rw [hWU, Submodule.map_subtype_top])
    exact Subrepresentation.toSubmodule_injective (by rw [hA]; rfl)

/-- The invariants of the `K`-representation on a `K`-stable subspace `U ≤ V` vanish as soon as
those of `ρ|_K` do. -/
lemma invariants_subrepresentation_eq_bot {K : Subgroup G} {U : Submodule L V}
    (hstab : IsStableUnder ρ K U)
    (hinv : Representation.invariants (ρ.comp K.subtype) = ⊥) :
    (Representation.subrepresentation (ρ.comp K.subtype) U hstab).invariants = ⊥ := by
  classical
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Representation.mem_invariants] at hx
  have hxv : (x : V) ∈ Representation.invariants (ρ.comp K.subtype) := by
    rw [Representation.mem_invariants]
    intro k
    have h := congrArg Subtype.val (hx k)
    simpa [Representation.subrepresentation, LinearMap.restrict_apply] using h
  rw [hinv, Submodule.mem_bot] at hxv
  exact Subtype.ext hxv

/-- A nonzero `K`-stable `K`-simple submodule of `V`, when `V ≠ 0`. -/
lemma exists_simple_stable_submodule [FiniteDimensional L V] {K : Subgroup G}
    (hV : (⊤ : Submodule L V) ≠ ⊥) :
    ∃ U : Submodule L V, U ≠ ⊥ ∧ IsStableUnder ρ K U ∧
      ∀ W : Submodule L V, W ≤ U → IsStableUnder ρ K W → W ≠ ⊥ → W = U := by
  classical
  suffices h : ∀ n, ∀ U : Submodule L V, Module.finrank L U = n → U ≠ ⊥ → IsStableUnder ρ K U →
      ∃ U' : Submodule L V, U' ≤ U ∧ U' ≠ ⊥ ∧ IsStableUnder ρ K U' ∧
        ∀ W, W ≤ U' → IsStableUnder ρ K W → W ≠ ⊥ → W = U' by
    obtain ⟨U, -, hne, hstab, hsimp⟩ :=
      h (Module.finrank L (⊤ : Submodule L V)) (⊤ : Submodule L V) rfl hV (fun s => by simp)
    exact ⟨U, hne, hstab, hsimp⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U hdim hne hstab
    by_cases hsimp : ∀ W, W ≤ U → IsStableUnder ρ K W → W ≠ ⊥ → W = U
    · exact ⟨U, le_rfl, hne, hstab, hsimp⟩
    · push Not at hsimp
      obtain ⟨W, hWU, hWstab, hWne, hWneU⟩ := hsimp
      have hlt : Module.finrank L W < n := by
        rw [← hdim]
        exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hWU hWneU)
      obtain ⟨U', hU'W, hU'ne, hU'stab, hU'simp⟩ :=
        ih (Module.finrank L W) hlt W rfl hWne hWstab
      exact ⟨U', hU'W.trans hWU, hU'ne, hU'stab, hU'simp⟩
end Core

section EquivariantProj

variable (ρ : Representation L G V)

/-- The supremum of a family of `K`-stable submodules is `K`-stable. -/
lemma iSup_stable {K : Subgroup G} {ι : Type*} (W : ι → Submodule L V)
    (h : ∀ i, IsStableUnder ρ K (W i)) : IsStableUnder ρ K (⨆ i, W i) := by
  intro k
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_iSup]
  refine iSup_le fun i => le_trans ?_ (le_iSup (fun i => W i) i)
  rw [Submodule.map_le_iff_le_comap]
  exact h i k

/-- **Maschke averaging.**  If `X ≤ Y` are `S`-stable subspaces of a representation of a finite
group `S` with `|S|` invertible in `L`, there is an `S`-equivariant projection of `V` onto `X`
along `Y` (i.e. fixing `X` pointwise and mapping `Y` into `X`). -/
theorem exists_stable_proj (S : Subgroup G) [Fintype ↥S] (hcard : (Nat.card ↥S : L) ≠ 0)
    {X Y : Submodule L V} (hXY : X ≤ Y) (hX : IsStableUnder ρ S X)
    (hY : IsStableUnder ρ S Y) :
    ∃ π : V →ₗ[L] V, (∀ x ∈ X, π x = x) ∧ (∀ y ∈ Y, π y ∈ X) ∧
      (∀ s : ↥S, π.comp (ρ (s : G)) = (ρ (s : G)).comp π) := by
  classical
  obtain ⟨q, hq⟩ := LinearMap.exists_leftInverse_of_injective X.subtype (Submodule.ker_subtype X)
  let p₀ : V →ₗ[L] V := X.subtype ∘ₗ q
  have hp₀X : ∀ x ∈ X, p₀ x = x := by
    intro x hx
    have h1 := congrArg (fun f : ↥X →ₗ[L] ↥X => f ⟨x, hx⟩) hq
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
    have h2 := congrArg Subtype.val h1
    simpa [p₀] using h2
  have hp₀mem : ∀ v : V, p₀ v ∈ X := fun v => (q v).2
  set π : V →ₗ[L] V :=
    (Nat.card ↥S : L)⁻¹ • ∑ s : ↥S, (ρ (s : G)) ∘ₗ p₀ ∘ₗ (ρ (((s⁻¹ : ↥S) : G))) with hπdef
  have hπapply : ∀ v : V,
      π v = (Nat.card ↥S : L)⁻¹ •
        ∑ s : ↥S, (ρ (s : G)) (p₀ ((ρ (((s⁻¹ : ↥S) : G))) v)) := by
    intro v
    rw [hπdef]
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
  refine ⟨π, ?_, ?_, ?_⟩
  · intro x hx
    have hterm : ∀ s : ↥S, (ρ (s : G)) (p₀ ((ρ (((s⁻¹ : ↥S) : G))) x)) = x := by
      intro s
      have h1 : (ρ (((s⁻¹ : ↥S) : G))) x ∈ X := hX (s⁻¹) hx
      rw [hp₀X _ h1, mul_apply_eq ρ (s : G) (((s⁻¹ : ↥S) : G)),
        show ((s : G) * (((s⁻¹ : ↥S) : G))) = 1 from by rw [Subgroup.coe_inv]; group, map_one]
      rfl
    rw [hπapply]
    simp only [hterm, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul L,
      Fintype.card_eq_nat_card, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  · intro y hy
    rw [hπapply]
    refine X.smul_mem _ (X.sum_mem fun s _ => ?_)
    exact hX s (hp₀mem _)
  · intro t
    ext v
    simp only [LinearMap.comp_apply]
    rw [hπapply, hπapply]
    simp only [map_smul, map_sum]
    congr 1
    -- reindex the sum by left multiplication with `t`
    rw [← Equiv.sum_comp (Equiv.mulLeft t)
      (fun s : ↥S => (ρ (s : G)) (p₀ ((ρ (((s⁻¹ : ↥S) : G))) ((ρ (t : G)) v))))]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Equiv.coe_mulLeft]
    show (ρ (((t * s : ↥S) : G))) (p₀ ((ρ ((((t * s)⁻¹ : ↥S) : G))) ((ρ (t : G)) v)))
      = (ρ (t : G)) ((ρ (s : G)) (p₀ ((ρ (((s⁻¹ : ↥S) : G))) v)))
    rw [mul_apply_eq ρ (t : G) (s : G)]
    congr 1
    rw [show (((t * s)⁻¹ : ↥S) : G) = ((s⁻¹ : ↥S) : G) * ((t⁻¹ : ↥S) : G) from by
        simp only [Subgroup.coe_inv, Subgroup.coe_mul, mul_inv_rev],
      map_mul, Module.End.mul_apply]
    have h2 : (ρ (((t⁻¹ : ↥S) : G))) ((ρ ((t : ↥S) : G)) v) = v := by
      rw [Subgroup.coe_inv]
      exact rho_inv_rho ρ (t : G) v
    rw [h2]

end EquivariantProj

section HomVanish

/-- **The key step of Feit--Thompson 3.16 (iii), `K`-equivariant form.** -/
theorem hom_vanish {p : ℕ} [Fact p.Prime] [CharP L p] [IsAlgClosed L] [Fintype G]
    (ρ : Representation L G V) [ρ.IsIrreducible] [FiniteDimensional L V]
    {K E : Subgroup G} (hKn : K.Normal) (hinf : K ⊓ E = ⊥) (hsup : K ⊔ E = ⊤)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set G) ≤ K)
    (hcop : ¬ p ∣ Nat.card G) {U : Submodule L V} (hU : U ≠ ⊥)
    (hUstab : IsStableUnder ρ K U)
    (hUsimp : ∀ W : Submodule L V, W ≤ U → IsStableUnder ρ K W → W ≠ ⊥ → W = U)
    (hinv : Representation.invariants (ρ.comp K.subtype) = ⊥)
    {g h : G} (hgE : g ∈ E) (hhE : h ∈ E) (hgh : g ≠ h) (f : V →ₗ[L] V)
    (hfK : ∀ k : ↥K, f.comp (ρ (k : G)) = (ρ (k : G)).comp f)
    (hfmap : ∀ u ∈ U, f (ρ g u) ∈ Submodule.map (ρ h) U) :
    ∀ u ∈ U, f (ρ g u) = 0 := by
  classical
  haveI : K.Normal := hKn
  by_cases hf0 : ∀ u ∈ U, f (ρ g u) = 0
  · exact hf0
  push Not at hf0
  obtain ⟨u₀, hu₀, hfu₀⟩ := hf0
  have hfne : ∃ u ∈ U, f (ρ g u) ≠ 0 := ⟨u₀, hu₀, hfu₀⟩
  have hinj : ∀ x ∈ Submodule.map (ρ g) U, f x = 0 → x = 0 := by
    intro x hx hfx
    have hZstab : IsStableUnder ρ K (Submodule.map (ρ g) U ⊓ Submodule.comap f ⊥) :=
      inf_stable ρ (map_rho_stable ρ hKn hUstab g) (comap_bot_stable ρ hfK)
    have hZle : Submodule.map (ρ g) U ⊓ Submodule.comap f ⊥ ≤ Submodule.map (ρ g) U :=
      inf_le_left
    have hZ : Submodule.map (ρ g) U ⊓ Submodule.comap f ⊥ = ⊥ := by
      by_contra hZne
      have hz : Submodule.map (ρ g) U ≤ Submodule.comap f ⊥ := by
        rw [← map_rho_simple ρ hKn hU hUstab hUsimp g _ hZle hZstab hZne]
        exact inf_le_right
      obtain ⟨u, hu, hfu⟩ := hfne
      exact hfu (by
        have := hz (Submodule.mem_map_of_mem hu)
        simpa only [Submodule.mem_comap, Submodule.mem_bot] using this)
    have hxZ : x ∈ Submodule.map (ρ g) U ⊓ Submodule.comap f ⊥ :=
      Submodule.mem_inf.mpr ⟨hx, by simpa only [Submodule.mem_comap, Submodule.mem_bot] using hfx⟩
    rw [hZ, Submodule.mem_bot] at hxZ
    exact hxZ
  have hsurj : ∀ y ∈ Submodule.map (ρ h) U, ∃ x ∈ Submodule.map (ρ g) U, f x = y := by
    have hMstab : IsStableUnder ρ K (Submodule.map f (Submodule.map (ρ g) U)) := by
      intro k z hz
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
      rw [Submodule.mem_comap]
      have h2 := congrArg (fun t : V →ₗ[L] V => t x) (hfK k)
      simp only [LinearMap.comp_apply] at h2
      rw [← h2]
      exact Submodule.mem_map_of_mem (map_rho_stable ρ hKn hUstab g k hx)
    have hMle : Submodule.map f (Submodule.map (ρ g) U) ≤ Submodule.map (ρ h) U := by
      rintro z ⟨x, hx, rfl⟩
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
      exact hfmap u hu
    have hMne : Submodule.map f (Submodule.map (ρ g) U) ≠ ⊥ := by
      intro hbot
      have hmem : f (ρ g u₀) ∈ Submodule.map f (Submodule.map (ρ g) U) :=
        Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hu₀)
      rw [hbot, Submodule.mem_bot] at hmem
      exact hfu₀ hmem
    have hM : Submodule.map f (Submodule.map (ρ g) U) = Submodule.map (ρ h) U :=
      map_rho_simple ρ hKn hU hUstab hUsimp h _ hMle hMstab hMne
    intro y hy
    rw [← hM] at hy
    obtain ⟨x, hx, hfy⟩ := Submodule.mem_map.mp hy
    exact ⟨x, hx, hfy⟩
  set σ : ↥K ≃* ↥K := MulAut.conjNormal (h⁻¹ * g) with hσdef
  set ψ : V →ₗ[L] V := (ρ h⁻¹) ∘ₗ f ∘ₗ (ρ g) with hψdef
  have hψapp : ∀ v : V, ψ v = ρ h⁻¹ (f (ρ g v)) := fun v => rfl
  have hψU : ∀ u ∈ U, ψ u ∈ U := by
    intro u hu
    obtain ⟨u'', hu'', hu''eq⟩ := Submodule.mem_map.mp (hfmap u hu)
    rw [hψapp, ← hu''eq, rho_inv_rho ρ h u'']
    exact hu''
  have hψσ : ∀ (k : ↥K) (v : V), ψ (ρ (k : G) v) = ρ ((σ k : ↥K) : G) (ψ v) := by
    intro k v
    have h1 : ψ (ρ (k : G) v) = ρ (h⁻¹ * (g * (k : G) * g⁻¹)) (f (ρ g v)) := by
      rw [hψapp]
      have e1 : ρ g (ρ (k : G) v) = ρ (g * (k : G)) v := mul_apply_eq ρ g (k : G) v
      rw [e1]
      have e2 : (ρ (g * (k : G)) : V →ₗ[L] V) = ρ (g * (k : G) * g⁻¹) * ρ g := by
        conv_lhs => rw [show g * (k : G) = (g * (k : G) * g⁻¹) * g from by group]
        rw [map_mul]
      rw [e2, Module.End.mul_apply]
      have e3 : f (ρ (g * (k : G) * g⁻¹) (ρ g v)) = ρ (g * (k : G) * g⁻¹) (f (ρ g v)) := by
        have hh := congrArg (fun t : V →ₗ[L] V => t (ρ g v))
          (hfK ⟨g * (k : G) * g⁻¹, hKn.conj_mem (k : G) k.2 g⟩)
        simpa only [LinearMap.comp_apply] using hh
      rw [e3, mul_apply_eq ρ h⁻¹ (g * (k : G) * g⁻¹) (f (ρ g v))]
    have h2 : ρ ((σ k : ↥K) : G) (ψ v) = ρ (h⁻¹ * (g * (k : G) * g⁻¹)) (f (ρ g v)) := by
      rw [hψapp]
      have e : ((σ k : ↥K) : G) = h⁻¹ * g * (k : G) * (h⁻¹ * g)⁻¹ := by
        simp only [σ, MulAut.conjNormal_apply]
      rw [e, mul_inv_rev, inv_inv]
      rw [mul_apply_eq ρ (h⁻¹ * g * (k : G) * (g⁻¹ * h)) h⁻¹ (f (ρ g v))]
      congr 1
      group
    rw [h1, h2]
  have hψU' : ∀ u ∈ U, ψ u ∈ U := hψU
  set ψU : ↥U →ₗ[L] ↥U := ψ.restrict hψU' with hψUdef
  have hψU_bij : Function.Bijective ψU := by
    constructor
    · intro x y hxy
      have h1 : ψ (x : V) = ψ (y : V) := by
        have := congrArg Subtype.val hxy
        simpa only [ψU, LinearMap.restrict_apply] using this
      have h2 : f (ρ g (x : V)) = f (ρ g (y : V)) := by
        have := congrArg (ρ h) h1
        simpa only [hψapp, rho_rho_inv ρ h] using this
      have h3 : ρ g (x : V) = ρ g (y : V) := by
        have h0 : f (ρ g (x : V) - ρ g (y : V)) = 0 := by rw [map_sub, h2, sub_self]
        have := hinj _ (Submodule.sub_mem (Submodule.map (ρ g) U)
          (Submodule.mem_map_of_mem x.2) (Submodule.mem_map_of_mem y.2)) h0
        rwa [sub_eq_zero] at this
      exact Subtype.ext (by
        have := congrArg (ρ g⁻¹) h3
        simpa only [rho_inv_rho ρ g] using this)
    · intro x
      obtain ⟨z, hz, hfz⟩ := hsurj (ρ h (x : V)) (Submodule.mem_map_of_mem x.2)
      obtain ⟨u', hu', rfl⟩ := Submodule.mem_map.mp hz
      refine ⟨⟨u', hu'⟩, ?_⟩
      apply Subtype.ext
      simp only [ψU, LinearMap.restrict_apply, hψapp, hfz, rho_inv_rho ρ h]
  have hfpf : ∀ k : ↥K, σ k = k → k = 1 := by
    intro k hk
    by_contra hkne
    have hkG : (k : G) ≠ 1 := fun hcon => hkne (Subtype.ext hcon)
    have h1 : (h⁻¹ * g) * (k : G) * (h⁻¹ * g)⁻¹ = (k : G) := by
      have := congrArg (fun t : ↥K => (t : G)) hk
      simpa only [σ, MulAut.conjNormal_apply] using this
    have hcomm : (h⁻¹ * g) * (k : G) = (k : G) * (h⁻¹ * g) := by
      calc (h⁻¹ * g) * (k : G) = ((h⁻¹ * g) * (k : G) * (h⁻¹ * g)⁻¹) * (h⁻¹ * g) := by group
        _ = (k : G) * (h⁻¹ * g) := by rw [h1]
    have hx1 : h⁻¹ * g ∈ K := by
      refine hcent (k : G) k.2 hkG ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hcomm.symm
    have hx2 : h⁻¹ * g ∈ E := E.mul_mem (E.inv_mem hhE) hgE
    have hx3 : h⁻¹ * g ∈ K ⊓ E := Subgroup.mem_inf.mpr ⟨hx1, hx2⟩
    rw [hinf, Subgroup.mem_bot] at hx3
    refine hgh ?_
    calc g = h * (h⁻¹ * g) := by group
      _ = h * 1 := by rw [hx3]
      _ = h := by rw [mul_one]
  have hcopK : ¬ p ∣ Nat.card ↥K := by
    intro hdvd
    obtain ⟨m, hm⟩ := hdvd
    exact hcop ⟨m * K.index, by rw [← Subgroup.card_mul_index K, hm, mul_assoc]⟩
  haveI hUirr : (Representation.subrepresentation (ρ.comp K.subtype) U hUstab).IsIrreducible :=
    subrepresentation_isIrreducible ρ hU hUstab hUsimp
  have hinvU : (Representation.subrepresentation (ρ.comp K.subtype) U hUstab).invariants = ⊥ :=
    invariants_subrepresentation_eq_bot ρ hUstab hinv
  have hψUσ : ∀ (k : ↥K) (u : ↥U),
      ψU ((Representation.subrepresentation (ρ.comp K.subtype) U hUstab) k u)
        = (Representation.subrepresentation (ρ.comp K.subtype) U hUstab) (σ k) (ψU u) := by
    intro k u
    apply Subtype.ext
    show ψ (ρ (k : G) (u : V)) = ρ ((σ k : ↥K) : G) (ψ (u : V))
    exact hψσ k (u : V)
  exfalso
  exact no_isFixedPointFree_semilinear_bijective
    (ρ := Representation.subrepresentation (ρ.comp K.subtype) U hUstab) hinvU hcopK σ hfpf ψU
    hψU_bij hψUσ

end HomVanish

section DirectSum

/-- The `E`-conjugates of a nonzero `K`-simple `K`-stable subspace are independent. -/
theorem iSupIndep_map_rho {p : ℕ} [Fact p.Prime] [CharP L p] [IsAlgClosed L] [Fintype G]
    (ρ : Representation L G V) [ρ.IsIrreducible] [FiniteDimensional L V]
    {K E : Subgroup G} (hKn : K.Normal) (hinf : K ⊓ E = ⊥) (hsup : K ⊔ E = ⊤)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set G) ≤ K)
    (hcop : ¬ p ∣ Nat.card G) {U : Submodule L V} (hU : U ≠ ⊥)
    (hUstab : IsStableUnder ρ K U)
    (hUsimp : ∀ W : Submodule L V, W ≤ U → IsStableUnder ρ K W → W ≠ ⊥ → W = U)
    (hinv : Representation.invariants (ρ.comp K.subtype) = ⊥) :
    iSupIndep (fun h : ↥E => Submodule.map (ρ ((h : ↥E) : G)) U) := by
  classical
  haveI : K.Normal := hKn
  have hcard : (Nat.card ↥K : L) ≠ 0 := by
    intro h0
    have hdvd : p ∣ Nat.card ↥K := (CharP.cast_eq_zero_iff L p (Nat.card ↥K)).mp h0
    obtain ⟨m, hm⟩ := hdvd
    exact hcop ⟨m * K.index, by rw [← Subgroup.card_mul_index K, hm, mul_assoc]⟩
  rw [iSupIndep_iff_supIndep_univ, Finset.supIndep_iff_disjoint_erase]
  intro h _
  set W : ↥E → Submodule L V := fun t => Submodule.map (ρ ((t : ↥E) : G)) U with hWdef
  set Y : Submodule L V := (Finset.univ.erase h).sup W with hYdef
  set X : Submodule L V := W h ⊓ Y with hXdef
  have hYstab : IsStableUnder ρ K Y := by
    intro k
    rw [hYdef]
    refine Finset.sup_le fun t ht => ?_
    exact le_trans (map_rho_stable ρ hKn hUstab ((t : ↥E) : G) k)
      (Submodule.comap_mono (Finset.le_sup (f := W) ht))
  have hXstab : IsStableUnder ρ K X :=
    inf_stable ρ (map_rho_stable ρ hKn hUstab ((h : ↥E) : G)) hYstab
  obtain ⟨π, hπX, hπY, hπcomm⟩ :=
    exists_stable_proj ρ K hcard (X := X) (Y := Y) inf_le_right hXstab hYstab
  rw [disjoint_iff_inf_le]
  intro x hx
  rw [Submodule.mem_bot]
  obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
  have hxY : x ∈ Y := by rw [hYdef]; exact hx2
  have hxX : x ∈ X := Submodule.mem_inf.mpr ⟨hx1, hxY⟩
  rw [hYdef, Finset.sup_eq_iSup] at hxY
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum W x).mp hxY
  have hπμ : ∀ t ∈ Finset.univ.erase h, π ((μ t : ↥(W t)) : V) = 0 := by
    intro t ht
    have htne : t ≠ h := fun hth => (Finset.mem_erase.mp ht).1 hth
    obtain ⟨u', hu', hu'eq⟩ := Submodule.mem_map.mp (μ t).2
    have hvan := hom_vanish ρ hKn hinf hsup hcent hcop hU hUstab hUsimp hinv
      (g := ((t : ↥E) : G)) (h := ((h : ↥E) : G)) t.2 h.2
      (fun hth => htne (Subtype.ext hth)) π hπcomm (fun u hu => ?_)
    · rw [← hu'eq]
      exact hvan u' hu'
    · have hmemY : (ρ ((t : ↥E) : G)) u ∈ Y := by
        rw [hYdef, hWdef]
        exact Finset.le_sup (f := W) ht (Submodule.mem_map_of_mem hu)
      exact (Submodule.mem_inf.mp (hπY _ hmemY)).1
  calc x = π x := (hπX x hxX).symm
    _ = π (∑ t ∈ Finset.univ.erase h, ((μ t : ↥(W t)) : V)) := by rw [hμ]
    _ = ∑ t ∈ Finset.univ.erase h, π ((μ t : ↥(W t)) : V) := map_sum π _ _
    _ = 0 := Finset.sum_eq_zero fun t ht => hπμ t ht

/-- The conjugates of a nonzero `K`-stable subspace span `V` (irreducibility of `ρ`). -/
theorem iSup_map_rho_eq_top {p : ℕ} [Fact p.Prime] [CharP L p] [Fintype G]
    (ρ : Representation L G V)
    [ρ.IsIrreducible] {K E : Subgroup G} (hKn : K.Normal) (hinf : K ⊓ E = ⊥)
    (hsup : K ⊔ E = ⊤) (hker : ¬ K ≤ ρ.ker) {U : Submodule L V} (hU : U ≠ ⊥)
    (hUstab : IsStableUnder ρ K U) :
    ⨆ t : ↥E, Submodule.map (ρ ((t : ↥E) : G)) U = ⊤ := by
  classical
  haveI : K.Normal := hKn
  set W : ↥E → Submodule L V := fun t => Submodule.map (ρ ((t : ↥E) : G)) U with hWdef
  set Y : Submodule L V := ⨆ t : ↥E, W t with hYdef
  have hYne : Y ≠ ⊥ := by
    intro hbot
    refine hU ?_
    have h1 : W 1 ≤ Y := by rw [hYdef]; exact le_iSup W 1
    have h2 : W 1 = ⊥ := le_bot_iff.mp (h1.trans (le_of_eq hbot))
    rw [hWdef] at h2
    have h3 : U = ⊥ := by
      have h4 : Submodule.map (ρ (1 : G)) U = ⊥ := h2
      rwa [map_one, Module.End.one_eq_id, Submodule.map_id] at h4
    exact h3
  have hYstabK : IsStableUnder ρ K Y := by
    intro k
    rw [hYdef]
    refine iSup_le fun t => ?_
    exact le_trans (map_rho_stable ρ hKn hUstab ((t : ↥E) : G) k)
      (Submodule.comap_mono (le_iSup W t))
  have hYstabE : ∀ e : ↥E, Y ≤ Y.comap (ρ ((e : ↥E) : G)) := by
    intro e
    rw [hYdef]
    refine iSup_le fun t => ?_
    rw [← Submodule.map_le_iff_le_comap, ← Submodule.map_comp]
    have h1 : ((ρ ((e : ↥E) : G)) ∘ₗ (ρ ((t : ↥E) : G))) = ρ (((e * t : ↥E) : G)) := by
      rw [← Module.End.mul_eq_comp, ← map_mul]
      rfl
    rw [h1]
    exact le_iSup W (e * t)
  have hYtop : Y = ⊤ := by
    have hstab : ∀ g : G, Y ≤ Y.comap (ρ g) := by
      intro g
      have hg : g ∈ K ⊔ E := by rw [hsup]; trivial
      obtain ⟨k, hk, e, he, hmul⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := K) (t := E) (x := g)).mp hg
      rw [← hmul]
      intro v hv
      rw [Submodule.mem_comap]
      rw [map_mul, Module.End.mul_apply]
      exact hYstabK ⟨k, hk⟩ (hYstabE ⟨e, he⟩ hv)
    rcases eq_bot_or_eq_top (⟨Y, hstab⟩ : Subrepresentation ρ) with hb | ht
    · exact absurd (congrArg Subrepresentation.toSubmodule hb) hYne
    · exact congrArg Subrepresentation.toSubmodule ht
  simpa [hYdef, hWdef] using hYtop

end DirectSum

/-- **The modular form of Feit--Thompson 3.16 (iii), fixed-point dimension form.** -/
theorem finrank_invariants_ge_of_irreducible {L : Type*} [Field L] [IsAlgClosed L] {p : ℕ}
    [Fact p.Prime] [CharP L p] {G : Type*} [Group G] [Fintype G] {V : Type*}
    [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    {K E E₀ : Subgroup G} (hKn : K.Normal) (hinf : K ⊓ E = ⊥) (hsup : K ⊔ E = ⊤)
    (hKne : K ≠ ⊥) (hEne : E ≠ ⊥)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set G) ≤ K)
    (hcop : ¬ p ∣ Nat.card G)
    (ρ : Representation L G V) [ρ.IsIrreducible]
    (hker : ¬ K ≤ ρ.ker) (hE₀ : E₀ ≤ E) :
    E₀.relIndex E ≤ Module.finrank L ↥(Representation.invariants (ρ.comp E₀.subtype)) := by
  classical
  have hV : (⊤ : Submodule L V) ≠ ⊥ := by
    intro hbot
    refine hker fun k hk => ?_
    rw [MonoidHom.mem_ker]
    ext v
    have hv : v = 0 := (Submodule.eq_bot_iff ⊤).mp hbot v trivial
    rw [hv]; simp
  have hinvK := invariants_comp_subtype_eq_bot ρ hKn hker
  obtain ⟨U, hU, hUstab, hUsimp⟩ := exists_simple_stable_submodule ρ hV
  set W : ↥E → Submodule L V := fun t => Submodule.map (ρ ((t : ↥E) : G)) U with hWdef
  have hind : iSupIndep W := iSupIndep_map_rho ρ hKn hinf hsup hcent hcop hU hUstab hUsimp hinvK
  have hsuptop : ⨆ t : ↥E, W t = ⊤ :=
    iSup_map_rho_eq_top ρ hKn hinf hsup hker hU hUstab
  have hne : W 1 ≠ ⊥ := by
    rw [hWdef]
    intro h2
    refine hU ?_
    have h4 : Submodule.map (ρ (1 : G)) U = ⊥ := h2
    rwa [map_one, Module.End.one_eq_id, Submodule.map_id] at h4
  have hperm : ∀ (e h : ↥E),
      Submodule.map ((ρ.comp E.subtype) e) (W h) = W (e * h) := by
    intro e h
    rw [hWdef]
    show Submodule.map (ρ ((e : ↥E) : G)) (Submodule.map (ρ ((h : ↥E) : G)) U)
      = Submodule.map (ρ (((e * h : ↥E)) : G)) U
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul]
    rfl
  have h := relIndex_le_finrank_invariants_of_iSupIndep_permuted (ρ := ρ.comp E.subtype)
    W hind hsuptop hperm hne (E₀.subgroupOf E)
  have hinv_eq :
      Representation.invariants ((ρ.comp E.subtype).comp (E₀.subgroupOf E).subtype)
        = Representation.invariants (ρ.comp E₀.subtype) := by
    ext v
    simp only [Representation.mem_invariants]
    constructor
    · intro hh y
      exact hh ⟨⟨(y : G), hE₀ y.2⟩, y.2⟩
    · intro hh x
      exact hh ⟨((x : ↥E) : G), x.2⟩
  have hfin : Module.finrank L
        ↥(Representation.invariants ((ρ.comp E.subtype).comp (E₀.subgroupOf E).subtype))
      = Module.finrank L ↥(Representation.invariants (ρ.comp E₀.subtype)) :=
    congrArg (fun s : Submodule L V => Module.finrank L ↥s) hinv_eq
  rw [hfin] at h
  exact h

end Work.CharPrelim

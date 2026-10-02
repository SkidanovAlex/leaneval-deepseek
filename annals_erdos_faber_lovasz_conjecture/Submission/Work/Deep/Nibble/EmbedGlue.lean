import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.EmbedAux
import Submission.Work.Deep.Nibble.EmbedStar
import Submission.Work.Deep.Nibble.EmbedDes
import Submission.Work.Deep.Nibble.Hstar_unif_linear
import Submission.Work.Deep.Nibble.EmbedCount

/-!
# The gluing: `𝓖 = T` copies of `𝓗*` with a design glued at every vertex

`GG hr D C U` is the hypergraph `𝓖` of `lem:embed` on `Fin T × V(𝓗*)`, and
`iotaG` is the embedding `ι : Fin N ↪ Fin T × V(𝓗*)` given by the copy `0`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

variable {N r : ℕ} {𝓗 : MultiHypergraph N}

/-- The vertex set of `𝓗`. -/
abbrev Verts (𝓗 : MultiHypergraph N) : Set (Fin N) := {v : Fin N | 0 < 𝓗.deg v}

/-- `𝓖`: the `T` copies of `𝓗*` with the design `des` glued at every vertex. -/
def GG (hr : 3 ≤ r) (D C : ℝ) (U : UnifData N r 𝓗) :
    Set (Set (Fin (T hr D C U) × Vstar 𝓗 r U.M)) :=
  Clone.glue (T hr D C U) (Hstar U) (des hr D C U)

/-- The embedding `ι : Fin N → Fin T × V(𝓗*)` on the copy `0`. -/
def iotaG (hr : 3 ≤ r) (D C : ℝ) (U : UnifData N r 𝓗) :
    Fin N → Fin (T hr D C U) × Vstar 𝓗 r U.M :=
  fun v => (⟨0, T_pos hr D C U⟩, old U v)

/-- The copy `0` of a subset of `V(𝓗*)`. -/
def copy0 (hr : 3 ≤ r) (D C : ℝ) (U : UnifData N r 𝓗) (f : Set (Vstar 𝓗 r U.M)) :
    Set (Fin (T hr D C U) × Vstar 𝓗 r U.M) :=
  (fun u => (⟨0, T_pos hr D C U⟩, u)) '' f

theorem iotaG_inj (hr : 3 ≤ r) {C D : ℝ} (U : UnifData N r 𝓗) :
    Function.Injective (iotaG hr D C U) := by
  rintro a b h
  exact old_inj U (Prod.ext_iff.mp h).2

theorem copy0_inter (hr : 3 ≤ r) (D C : ℝ) (U : UnifData N r 𝓗)
    (g A : Set (Vstar 𝓗 r U.M)) :
    copy0 hr D C U g ∩ copy0 hr D C U A = copy0 hr D C U (g ∩ A) :=
  (Set.image_inter (by rintro a b h; exact (Prod.ext_iff.mp h).2)).symm

theorem copy0_iota (hr : 3 ≤ r) (D C : ℝ) (U : UnifData N r 𝓗) (S : Set (Fin N)) :
    copy0 hr D C U (old U '' S) = iotaG hr D C U '' S := by
  ext x; constructor
  · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨old U v, ⟨v, hv, rfl⟩, rfl⟩

theorem copy0_inj (hr : 3 ≤ r) (D C : ℝ) (U : UnifData N r 𝓗) :
    Function.Injective (copy0 hr D C U) :=
  Set.image_injective.mpr (by rintro a b h; exact (Prod.ext_iff.mp h).2)

theorem GG_ncard (hr : 3 ≤ r) (D C : ℝ) (U : UnifData N r 𝓗) :
    ∀ f ∈ GG hr D C U, f.ncard = r :=
  Clone.glue_ncard (Hstar_unif_linear 𝓗 U (by omega)).1 (des_ncard hr D C U)

theorem GG_linear (hr : 3 ≤ r) (D C : ℝ) (U : UnifData N r 𝓗) :
    ∀ ⦃f⦄, f ∈ GG hr D C U → ∀ ⦃f'⦄, f' ∈ GG hr D C U → f ≠ f' →
      (f ∩ f').Subsingleton :=
  Clone.glue_linear (Hstar_unif_linear 𝓗 U (by omega)).2 (des_linear hr D C U)

/-- The degree of `𝓖` at every clone of `u` is `mdeg D C U u`. -/
theorem GG_deg (hr : 3 ≤ r) (D C : ℝ) (U : UnifData N r 𝓗)
    (i : Fin (T hr D C U)) (u : Vstar 𝓗 r U.M) :
    ({f ∈ GG hr D C U | (i, u) ∈ f} :
        Set (Set (Fin (T hr D C U) × Vstar 𝓗 r U.M))).ncard = mdeg D C U u := by
  have h1 : ({g ∈ Hstar U | u ∈ g} : Set (Set (Vstar 𝓗 r U.M))).ncard = HstarDeg U u :=
    HstarDeg_def U u
  calc ({f ∈ GG hr D C U | (i, u) ∈ f} : Set (Set (Fin (T hr D C U) × Vstar 𝓗 r U.M))).ncard
      = ({g ∈ Hstar U | u ∈ g} : Set (Set (Vstar 𝓗 r U.M))).ncard
        + ({E ∈ des hr D C U u | i ∈ E} : Set (Set (Fin (T hr D C U)))).ncard := by
        rw [GG]
        exact Clone.glue_deg (by omega) (Hstar_unif_linear 𝓗 U (by omega)).1
          (des_ncard hr D C U) i u
    _ = HstarDeg U u + dprime D C U u := by rw [h1, des_deg hr D C U u]
    _ = mdeg D C U u := by
        rw [dprime, mdeg]
        exact Nat.add_sub_cancel' (le_max_left _ _)

/-- **The degrees of `𝓖` lie in `[D - C, D]`.** -/
theorem mdeg_bounds (hr : 3 ≤ r) {C D : ℝ} (hC1 : 1 ≤ C) (hD0 : 0 < D) (hD1 : 1 ≤ D)
    (U : UnifData N r 𝓗) (hdegD : ∀ v : Fin N, (𝓗.deg v : ℝ) ≤ D)
    (u : Vstar 𝓗 r U.M) :
    D - C ≤ (mdeg D C U u : ℝ) ∧ (mdeg D C U u : ℝ) ≤ D := by
  constructor
  · have h1 : (⌈D - C⌉₊ : ℝ) ≤ (mdeg D C U u : ℝ) := by
      rw [mdeg]
      exact_mod_cast le_max_right (HstarDeg U u) ⌈D - C⌉₊
    have h2 := Nat.le_ceil (D - C)
    linarith
  · have h1 : (HstarDeg U u : ℝ) ≤ D := HstarDeg_le U (by omega) hD1 hdegD u
    have h2 : (⌈D - C⌉₊ : ℝ) ≤ D := natCeil_sub_le hC1 hD0
    calc (mdeg D C U u : ℝ) = (max (HstarDeg U u) ⌈D - C⌉₊ : ℕ) := by rw [mdeg]
      _ = max (HstarDeg U u : ℝ) (⌈D - C⌉₊ : ℝ) := by rw [Nat.cast_max]
      _ ≤ D := max_le h1 h2

/-- At a non-isolated old vertex the degree of `𝓖` is exactly `𝓗.deg v`. -/
theorem mdeg_old (hr : 3 ≤ r) {C D : ℝ} (hD0 : 0 < D) (U : UnifData N r 𝓗)
    (hdegC : ∀ v : Fin N, 0 < 𝓗.deg v → D - C ≤ (𝓗.deg v : ℝ))
    {v : Fin N} (hv : 0 < 𝓗.deg v) : mdeg D C U (old U v) = 𝓗.deg v := by
  simp only [mdeg, HstarDeg_def, Hstar_deg_old U (by omega) v]
  refine max_eq_left ?_
  rw [Nat.ceil_le]
  exact hdegC v hv

/-- **The identification `κ` for `𝓖`.** -/
theorem GG_ident (hr : 3 ≤ r) (hlin : 𝓗.IsLinear) {C D : ℝ} (hD0 : 0 < D)
    (U : UnifData N r 𝓗)
    (hdegC : ∀ v : Fin N, 0 < 𝓗.deg v → D - C ≤ (𝓗.deg v : ℝ)) :
    ∃ κ : ({e : Set (Fin N) // e ∈ 𝓗.edges} ⊕ SC 𝓗) ≃
        {f : Set (Fin (T hr D C U) × Vstar 𝓗 r U.M) // f ∈ GG hr D C U ∧
          (f ∩ iotaG hr D C U '' Verts 𝓗).Nonempty},
      (∀ (e : Set (Fin N)) (he : e ∈ 𝓗.edges),
        ((κ (Sum.inl ⟨e, he⟩) : Set (Fin (T hr D C U) × Vstar 𝓗 r U.M))
          ∩ iotaG hr D C U '' Verts 𝓗) = iotaG hr D C U '' e) ∧
      (∀ (p : SC 𝓗),
        ((κ (Sum.inr p) : Set (Fin (T hr D C U) × Vstar 𝓗 r U.M))
          ∩ iotaG hr D C U '' Verts 𝓗) = {iotaG hr D C U p.1.1}) := by
  classical
  obtain ⟨κ₀, hκ₀e, hκ₀s⟩ := Hstar_ident U (by omega) hlin
  have hdprime : ∀ v : Fin N, 0 < 𝓗.deg v → dprime D C U (old U v) = 0 := by
    intro v hv
    simp only [dprime_eq_zero_iff, HstarDeg_def, Hstar_deg_old U (by omega) v]
    rw [Nat.ceil_le]
    exact hdegC v hv
  have hmeet : ∀ a : ({e : Set (Fin N) // e ∈ 𝓗.edges} ⊕ SC 𝓗),
      (copy0 hr D C U ((κ₀ a : Set (Vstar 𝓗 r U.M))) ∩ iotaG hr D C U '' Verts 𝓗).Nonempty := by
    intro a
    obtain ⟨x, hx1, hx2⟩ := (κ₀ a).2.2
    obtain ⟨v, hv, rfl⟩ := hx2
    exact ⟨iotaG hr D C U v, ⟨old U v, hx1, rfl⟩, ⟨v, hv, rfl⟩⟩
  let F : ({e : Set (Fin N) // e ∈ 𝓗.edges} ⊕ SC 𝓗) →
      {f : Set (Fin (T hr D C U) × Vstar 𝓗 r U.M) // f ∈ GG hr D C U ∧
        (f ∩ iotaG hr D C U '' Verts 𝓗).Nonempty} :=
    fun a => ⟨copy0 hr D C U ((κ₀ a : Set (Vstar 𝓗 r U.M))),
      Or.inl ⟨(κ₀ a).1, (κ₀ a).2.1, ⟨⟨0, T_pos hr D C U⟩, rfl⟩⟩, hmeet a⟩
  have hinj : Function.Injective F := by
    intro a b h
    have h1 : copy0 hr D C U ((κ₀ a : Set (Vstar 𝓗 r U.M)))
        = copy0 hr D C U ((κ₀ b : Set (Vstar 𝓗 r U.M))) := congrArg Subtype.val h
    exact κ₀.injective (Subtype.ext (copy0_inj hr D C U h1))
  have hsurj : Function.Surjective F := by
    rintro ⟨f, hf, hm⟩
    rw [GG] at hf
    rcases hf with ⟨g, hg, i, rfl⟩ | ⟨u, E, hE, rfl⟩
    · obtain ⟨y, hyf, hyV⟩ := hm
      obtain ⟨v, hv, rfl⟩ := hyV
      obtain ⟨u', hu', huu⟩ := hyf
      have hi : i = ⟨0, T_pos hr D C U⟩ := (Prod.ext_iff.mp huu).1
      have hu'v : u' = old U v := (Prod.ext_iff.mp huu).2
      subst hi
      have hgv : old U v ∈ g := by rw [← hu'v]; exact hu'
      obtain ⟨b, hb⟩ := κ₀.surjective ⟨g, hg, ⟨old U v, hgv, ⟨v, hv, rfl⟩⟩⟩
      refine ⟨b, Subtype.ext ?_⟩
      have hgb : (κ₀ b : Set (Vstar 𝓗 r U.M)) = g := congrArg Subtype.val hb
      show copy0 hr D C U ((κ₀ b : Set (Vstar 𝓗 r U.M)))
        = (fun u => (⟨0, T_pos hr D C U⟩, u)) '' g
      rw [hgb]
      rfl
    · exfalso
      obtain ⟨y, hyf, hyV⟩ := hm
      obtain ⟨v, hv, rfl⟩ := hyV
      obtain ⟨i', hi', hiu⟩ := hyf
      have hu : u = old U v := (Prod.ext_iff.mp hiu).2
      have hE' : E ∈ des hr D C U (old U v) := hu ▸ hE
      rw [des_empty_of_dprime_zero hr D C U (old U v) (hdprime v hv)] at hE'
      exact hE'
  refine ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro e he
    show (copy0 hr D C U ((κ₀ (Sum.inl ⟨e, he⟩) : Set (Vstar 𝓗 r U.M)))
      ∩ iotaG hr D C U '' Verts 𝓗) = iotaG hr D C U '' e
    rw [← copy0_iota hr D C U (Verts 𝓗), copy0_inter hr D C U, hκ₀e e he,
      copy0_iota hr D C U e]
  · intro p
    show (copy0 hr D C U ((κ₀ (Sum.inr p) : Set (Vstar 𝓗 r U.M)))
      ∩ iotaG hr D C U '' Verts 𝓗) = {iotaG hr D C U p.1.1}
    rw [← copy0_iota hr D C U (Verts 𝓗), copy0_inter hr D C U, hκ₀s p]
    ext x; constructor
    · rintro ⟨u, hu, rfl⟩
      rw [Set.mem_singleton_iff] at hu ⊢
      rw [hu]
      rfl
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      exact ⟨old U p.1.1, rfl, hx.symm⟩

end

end Work.Deep.Nibble

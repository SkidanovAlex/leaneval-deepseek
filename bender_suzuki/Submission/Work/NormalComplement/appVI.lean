import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.CharCore.Defs
import Submission.Work.CharCore.Main
import Submission.Work.Induction.Defs
import Submission.Work.Induction.Basic
import Submission.Work.Induction.Bridge
import Submission.Work.Induction.All
import Submission.Work.Coherence.Defs
import Submission.Work.Coherence.Basic
import Submission.Work.Coherence.All
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.TI.cfInner_indFun_eq_of_TISet
import Submission.Work.Clifford.All
import Submission.Work.CohApps.sum_irr_deg_sq_le_ker
import Submission.Work.NormalComplement.permutation_character_facts
import Submission.Work.NormalComplement.frobenius_kernel_irr
import Submission.Work.NormalComplement.coherent_exceptional_data_fixed
import Submission.Work.NormalComplement.rat_eq_int_of_isIntegral
import Submission.Work.NormalComplement.sup_eq_top_of_card_mul
import Submission.Work.ZassenhausPSL2.ZData.ExcCharSetup
import Submission.Work.ZassenhausPSL2.exc_char_coherent

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Classical MulAction
open scoped Pointwise

namespace Work.NormalComplement

variable {W : Type*} [Group W] [Finite W] {I : Type*} [Fintype I] [MulAction W I]

/-! ## 1. The regular subgroup: elementary structure

Throughout, `K ≤ W` acts *regularly* on `I` (`∀ i j, ∃! k : K, (k : W) • i = j`) and
`C_W(k) = K` for every `k ∈ K^#`.  This section records the elementary consequences. -/

section Regular

variable {K : Subgroup W}

/-- `K` acts freely: the only element of `K` fixing a point is `1`. -/
theorem K_smul_eq_self_iff (hreg : ∀ i j : I, ∃! k : K, (k : W) • i = j) (k : K) (i : I) :
    (k : W) • i = i ↔ k = 1 := by
  constructor
  · intro h
    exact (hreg i i).unique h (by simp)
  · intro h
    simp [h]

/-- The element of `K` carrying `i` to `j` is the chosen one. -/
theorem K_smul_eq_iff (hreg : ∀ i j : I, ∃! k : K, (k : W) • i = j) (i j : I) (k : K) :
    (k : W) • i = j ↔ k = Classical.choose (hreg i j).exists := by
  constructor
  · intro h
    exact (hreg i j).unique h (Classical.choose_spec (hreg i j).exists)
  · intro h
    rw [h]
    exact Classical.choose_spec (hreg i j).exists

theorem K_pretransitive (hreg : ∀ i j : I, ∃! k : K, (k : W) • i = j) :
    IsPretransitive K I :=
  MulAction.isPretransitive_iff K I |>.mpr fun i j =>
    ⟨Classical.choose (hreg i j).exists, Classical.choose_spec (hreg i j).exists⟩

theorem W_pretransitive (hreg : ∀ i j : I, ∃! k : K, (k : W) • i = j) :
    IsPretransitive W I :=
  MulAction.isPretransitive_iff W I |>.mpr fun i j =>
    ⟨(Classical.choose (hreg i j).exists : K), Classical.choose_spec (hreg i j).exists⟩

/-- `K` is nontrivial as soon as `1 < |I|`. -/
theorem K_ne_bot (hI : 1 < Fintype.card I)
    (hreg : ∀ i j : I, ∃! k : K, (k : W) • i = j) : K ≠ ⊥ := by
  intro hbot
  have hsub : Subsingleton I := ⟨fun i j => by
    obtain ⟨k, hk⟩ := (hreg i j).exists
    have hk1 : (k : W) = 1 := by
      have : (k : W) ∈ (⊥ : Subgroup W) := by rw [← hbot]; exact k.2
      simpa using this
    rw [hk1] at hk
    simpa using hk⟩
  have := Fintype.card_le_one_iff_subsingleton.mpr hsub
  omega

/-- `K` is abelian, because every element of `K^#` has centralizer `K`. -/
theorem K_commutative
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) = K) :
    ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
  intro a ha b hb
  by_cases ha1 : a = 1
  · subst ha1; simp
  · have hmem : b ∈ Subgroup.centralizer ({a} : Set W) := by
      rw [hcent a ha ha1]; exact hb
    exact (Subgroup.mem_centralizer_singleton_iff.mp hmem).symm

/-- Every element of `W` is a product `k * h` with `k ∈ K` and `h` in the point stabilizer. -/
theorem mul_K_stabilizer {α : I} (hreg : ∀ i j : I, ∃! k : K, (k : W) • i = j)
    (w : W) : ∃ k : K, ∃ h ∈ MulAction.stabilizer W α, w = (k : W) * h := by
  obtain ⟨k, hk⟩ := (hreg α (w • α)).exists
  refine ⟨k, ((k : W)⁻¹ * w), ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff]
    show ((k : W)⁻¹ * w) • α = α
    rw [mul_smul, ← hk, inv_smul_smul]
  · rw [← mul_assoc, mul_inv_cancel, one_mul]

/-- The point stabilizer meets `K` trivially. -/
theorem inf_stabilizer_bot {α : I} (hreg : ∀ i j : I, ∃! k : K, (k : W) • i = j) :
    K ⊓ MulAction.stabilizer W α = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro k ⟨hkK, hkH⟩
  have hfix : (k : W) • α = α := MulAction.mem_stabilizer_iff.mp hkH
  have := (K_smul_eq_self_iff hreg ⟨k, hkK⟩ α).mp hfix
  simpa using this

end Regular

/-! ## 2. Membership in a conjugate subgroup -/

/-- `x` lies in the conjugate `gHg^{-1}` of `H` iff `g⁻¹xg ∈ H`. -/
theorem mem_conj_iff {H : Subgroup W} {g x : W} :
    x ∈ Submission.Blueprint.conj g H ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h : g * y * g⁻¹ = x := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hyx
    rw [← h]
    have h2 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [h2]; exact hy
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

/-- `(MulAut.conj g).toMonoidHom` composed with `(MulAut.conj g⁻¹).toMonoidHom` is the
identity. -/
theorem conj_comp_conj_inv (g : W) :
    (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id W := by
  ext x
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]
  group

/-- `(MulAut.conj g⁻¹).toMonoidHom` composed with `(MulAut.conj g).toMonoidHom` is the
identity. -/
theorem conj_inv_comp_conj (g : W) :
    (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id W := by
  ext x
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]
  group

/-- Conjugating a conjugate by the inverse gives back the original subgroup. -/
theorem conj_inv_conj (g : W) (H : Subgroup W) :
    Submission.Blueprint.conj g⁻¹ (Submission.Blueprint.conj g H) = H := by
  show Subgroup.map (MulAut.conj g⁻¹).toMonoidHom
      (Subgroup.map (MulAut.conj g).toMonoidHom H) = H
  rw [Subgroup.map_map, conj_inv_comp_conj, Subgroup.map_id]

/-- Conjugating a conjugate gives back the original subgroup. -/
theorem conj_conj_inv (g : W) (H : Subgroup W) :
    Submission.Blueprint.conj g (Submission.Blueprint.conj g⁻¹ H) = H := by
  show Subgroup.map (MulAut.conj g).toMonoidHom
      (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom H) = H
  rw [Subgroup.map_map, conj_comp_conj_inv, Subgroup.map_id]

variable {K : Subgroup W}

/-- **`K` is a T.I. subgroup.**  Let `K` act regularly on `I` and suppose `C_W(k) = K` for
every `k ∈ K^#`.  Then `K ⊓ K^g = 1` for every `g ∉ N_W(K)`.

Indeed, if `1 ≠ x ∈ K ⊓ K^g` then `K` is abelian, so `K^g ≤ C_W(x) = K`; likewise
`K^{g⁻¹} ≤ C_W(g⁻¹xg) = K`, and conjugating this by `g` gives `K ≤ K^g`; hence `K^g = K`
and `g ∈ N_W(K)`. -/
theorem K_isTI (hreg : ∀ i j : I, ∃! k : K, (k : W) • i = j)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) = K) :
    ∀ g : W, g ∉ Subgroup.normalizer (K : Set W) →
      K ⊓ Submission.Blueprint.conj g K = ⊥ := by
  -- an element of `K#` lying also in `K^j` forces `K^j ≤ K` (both are abelian)
  have key : ∀ j u : W, u ∈ K → u ∈ Submission.Blueprint.conj j K → u ≠ 1 →
      Submission.Blueprint.conj j K ≤ K := by
    intro j u huK huJ hu1
    have hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := K_commutative hcent
    have hC : Subgroup.centralizer ({u} : Set W) = K := hcent u huK hu1
    have habel : ∀ a ∈ (Submission.Blueprint.conj j K : Set W),
        ∀ b ∈ Submission.Blueprint.conj j K, a * b = b * a := by
      intro a ha b hb
      have ha' : j⁻¹ * a * j ∈ K := mem_conj_iff.mp ha
      have hb' : j⁻¹ * b * j ∈ K := mem_conj_iff.mp hb
      have h := hcomm (j⁻¹ * a * j) ha' (j⁻¹ * b * j) hb'
      have h2 := congrArg (fun z => j * z * j⁻¹) h
      simpa [mul_assoc] using h2
    intro y hy
    rw [← hC, Subgroup.mem_centralizer_singleton_iff]
    exact habel y hy u huJ
  intro g hg
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨hxK, hxg⟩
  by_contra hx1
  have hKg : Submission.Blueprint.conj g K ≤ K := key g x hxK hxg hx1
  -- `g⁻¹ x g ∈ K^#` lies in `K^{g⁻¹}`
  have hyK : g⁻¹ * x * g ∈ K := mem_conj_iff.mp hxg
  have hyJ : g⁻¹ * x * g ∈ Submission.Blueprint.conj g⁻¹ K := by
    rw [mem_conj_iff]
    have h2 : (g⁻¹)⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [h2]; exact hxK
  have hy1 : g⁻¹ * x * g ≠ 1 := by
    intro h
    apply hx1
    have h2 := congrArg (fun z => g * z * g⁻¹) h
    simpa [mul_assoc] using h2
  have hKginv : Submission.Blueprint.conj g⁻¹ K ≤ K := key g⁻¹ _ hyK hyJ hy1
  have hle : K ≤ Submission.Blueprint.conj g K := by
    have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hKginv
    rw [Subgroup.map_map, conj_comp_conj_inv, Subgroup.map_id] at h
    exact h
  have heq : Submission.Blueprint.conj g K = K := le_antisymm hKg hle
  have heq' : Submission.Blueprint.conj g⁻¹ K = K := by
    have h := congrArg (Submission.Blueprint.conj g⁻¹) heq
    rw [conj_inv_conj] at h
    exact h.symm
  refine hg ?_
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have h1 : g * h * g⁻¹ ∈ Submission.Blueprint.conj g K := by
      refine Subgroup.mem_map.mpr ⟨h, hh, ?_⟩
      exact MulAut.conj_apply g h
    rwa [heq] at h1
  · intro hh
    have h2 : h ∈ Submission.Blueprint.conj g⁻¹ K := by
      rw [mem_conj_iff]
      simpa using hh
    rwa [heq'] at h2

/-- The kernel of the action meets the normalizer of `K` trivially.

If `z` acts trivially and normalises `K`, then for every `k ∈ K` the element `z k z⁻¹ k⁻¹` lies in
`K` and fixes every point, hence is `1`; so `z` centralises `K`.  Taking `k ∈ K^#` we get
`z ∈ C_W(k) = K`, and `K` acts freely, so `z = 1`. -/
theorem ker_inf_normalizer_eq_bot (hI : 1 < Fintype.card I)
    (hreg : ∀ i j : I, ∃! k : K, (k : W) • i = j)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) = K) :
    (MulAction.toPermHom W I).ker ⊓ Subgroup.normalizer (K : Set W) = ⊥ := by
  classical
  haveI : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  rw [Subgroup.mem_inf] at hz
  obtain ⟨hzk, hzn⟩ := hz
  have hzact : ∀ i : I, z • i = i := fun i => by
    have h := congrArg (fun f : Equiv.Perm I => f i) (MonoidHom.mem_ker.mp hzk)
    simpa [MulAction.toPermHom_apply, MulAction.toPerm_apply] using h
  have hzacti : ∀ i : I, z⁻¹ • i = i := fun i => by
    have hmem : z⁻¹ ∈ (MulAction.toPermHom W I).ker :=
      (MulAction.toPermHom W I).ker.inv_mem hzk
    have h := congrArg (fun f : Equiv.Perm I => f i) (MonoidHom.mem_ker.mp hmem)
    simpa [MulAction.toPermHom_apply, MulAction.toPerm_apply] using h
  obtain ⟨k, hk⟩ : ∃ k : K, k ≠ 1 :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (K_ne_bot hI hreg)
  have hznk : z * (k : W) * z⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp hzn (k : W)).mp k.2
  have hmemK : z * (k : W) * z⁻¹ * (k : W)⁻¹ ∈ K := K.mul_mem hznk (K.inv_mem k.2)
  have hkk : ∀ i : I, (k : W) • ((k : W)⁻¹ • i) = i := fun i => by
    rw [← mul_smul, mul_inv_cancel, one_smul]
  have hfix : (⟨z * (k : W) * z⁻¹ * (k : W)⁻¹, hmemK⟩ : K) • (Classical.arbitrary I)
      = Classical.arbitrary I := by
    show (z * (k : W) * z⁻¹ * (k : W)⁻¹) • (Classical.arbitrary I) = Classical.arbitrary I
    rw [mul_smul, mul_smul, mul_smul, hzacti, hkk, hzact]
  have hone : (⟨z * (k : W) * z⁻¹ * (k : W)⁻¹, hmemK⟩ : K) = 1 :=
    (K_smul_eq_self_iff hreg _ (Classical.arbitrary I)).mp hfix
  have hconj : z * (k : W) * z⁻¹ = (k : W) := by
    have h2 : z * (k : W) * z⁻¹ * (k : W)⁻¹ = (1 : W) :=
      congrArg (fun x : K => (x : W)) hone
    exact mul_inv_eq_one.mp h2
  have hcz : z ∈ Subgroup.centralizer ({(k : W)} : Set W) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 := congrArg (fun w => w * z) hconj
    simpa [mul_assoc] using h2
  have hzK : z ∈ K := by
    have hc := hcent (k : W) k.2 (fun h => hk (Subtype.ext h))
    rw [hc] at hcz
    exact hcz
  have hz1 : (⟨z, hzK⟩ : K) = 1 :=
    (K_smul_eq_self_iff hreg ⟨z, hzK⟩ (Classical.arbitrary I)).mp (by
      show z • (Classical.arbitrary I) = Classical.arbitrary I
      exact hzact _)
  exact congrArg (fun x : K => (x : W)) hz1

/-! ## 3. The permutation character counts fixed points -/

/-- **The permutation character computes the number of fixed points.**  If `W` acts transitively
on `I`, then for every `g : W` the induced function `Ind_{W_α}^W 1` takes at `g` the value
`#{i : I | g • i = i}`.

Indeed `Ind_{W_α}^W 1 g = |W_α|⁻¹ · #{x : W | x g x⁻¹ ∈ W_α}`, and this last set is
`|W_α|`-to-one onto the fixed points of `g` under `x ↦ x • α`. -/
theorem indFun_triv_apply_eq_fixedBy [Fintype W]
    (htr : MulAction.IsPretransitive W I) (α : I) (g : W) :
    Work.Induction.indFun (MulAction.stabilizer W α)
        (fun _ : MulAction.stabilizer W α => (1 : ℂ)) g
      = ((Nat.card (MulAction.fixedBy I g)) : ℂ) := by
  classical
  set S : Subgroup W := MulAction.stabilizer W α
  -- ### Step 1: the defining sum is a cardinality
  have hstep1 : Work.Induction.indFun S (fun _ : S => (1 : ℂ)) g
      = (Nat.card S : ℂ)⁻¹ *
          ((Finset.univ.filter (fun x : W => x * g * x⁻¹ ∈ S)).card : ℂ) := by
    rw [Work.Induction.indFun_apply_def]
    congr 1
    rw [← Finset.sum_boole (fun x : W => x * g * x⁻¹ ∈ S) Finset.univ]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : x * g * x⁻¹ ∈ S
    · simp [h]
    · simp [h]
  -- ### Step 2: replace `x g x⁻¹` by `x⁻¹ g x` (substitute `x ↦ x⁻¹`)
  have hstep2 : (Finset.univ.filter (fun x : W => x * g * x⁻¹ ∈ S)).card
      = (Finset.univ.filter (fun x : W => x⁻¹ * g * x ∈ S)).card := by
    refine Finset.card_bij (fun x _ => x⁻¹) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      simpa using hx
    · intro x _ y _ hxy
      exact inv_injective hxy
    · intro b hb
      refine ⟨b⁻¹, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      simpa using hb
  -- ### Step 3: count by the fibres of `x ↦ x • α`
  have hfiber : ∀ b ∈ (MulAction.fixedBy I g).toFinset,
      ((Finset.univ.filter (fun x : W => x⁻¹ * g * x ∈ S)).filter
          (fun x => x • α = b)).card = Nat.card S := by
    intro b hb
    have hb' : g • b = b := by
      simpa only [Set.mem_toFinset, MulAction.mem_fixedBy] using hb
    obtain ⟨y, hy⟩ := htr.exists_smul_eq α b
    have hcard : (Finset.univ.filter (fun x : W => x • α = b)).card = Nat.card S := by
      let e : S ≃ {x : W // x • α = b} :=
        { toFun := fun s => ⟨y * s, by
            show (y * (s : W)) • α = b
            rw [mul_smul, MulAction.mem_stabilizer_iff.mp s.2, hy]⟩
          invFun := fun x => ⟨y⁻¹ * x.1, by
            rw [MulAction.mem_stabilizer_iff]
            show (y⁻¹ * x.1) • α = α
            rw [mul_smul, x.2, ← hy, inv_smul_smul]⟩
          left_inv := fun s => Subtype.ext (by show y⁻¹ * (y * (s : W)) = (s : W); group)
          right_inv := fun x => Subtype.ext (by show y * (y⁻¹ * x.1) = x.1; group) }
      have h1 : Nat.card {x : W // x • α = b}
          = (Finset.univ.filter (fun x : W => x • α = b)).card := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_ofFinset _ (fun x => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact Iff.rfl)
      rw [← h1, ← Nat.card_congr e]
    have hsame : ((Finset.univ.filter (fun x : W => x⁻¹ * g * x ∈ S)).filter
          (fun x => x • α = b)).card
        = (Finset.univ.filter (fun x : W => x • α = b)).card := by
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact h.2
      · intro hx
        refine ⟨?_, hx⟩
        show (x⁻¹ * g * x) • α = α
        rw [mul_smul, mul_smul, hx, hb', ← hx, inv_smul_smul]
    rw [hsame, hcard]
  have hstep3 : (Finset.univ.filter (fun x : W => x⁻¹ * g * x ∈ S)).card
      = Nat.card (MulAction.fixedBy I g) * Nat.card S := by
    have hmap : Set.MapsTo (fun x : W => x • α)
        ↑(Finset.univ.filter (fun x : W => x⁻¹ * g * x ∈ S))
        ↑((MulAction.fixedBy I g).toFinset) := by
      intro x hx
      change x • α ∈ ↑((MulAction.fixedBy I g).toFinset)
      rw [Set.mem_toFinset, MulAction.mem_fixedBy]
      have hxS : (x⁻¹ * g * x) • α = α := by
        have hmem : x⁻¹ * g * x ∈ S := by simpa using hx
        exact MulAction.mem_stabilizer_iff.mp hmem
      calc g • (x • α) = (g * x) • α := (mul_smul g x α).symm
        _ = (x * (x⁻¹ * g * x)) • α := by congr 1; group
        _ = x • ((x⁻¹ * g * x) • α) := mul_smul x (x⁻¹ * g * x) α
        _ = x • α := by rw [hxS]
    have hsum : (∑ b ∈ (MulAction.fixedBy I g).toFinset,
          ((Finset.univ.filter (fun x : W => x⁻¹ * g * x ∈ S)).filter
              (fun x => x • α = b)).card)
        = ∑ _b ∈ (MulAction.fixedBy I g).toFinset, Nat.card S :=
      Finset.sum_congr rfl (fun b hb => hfiber b hb)
    rw [Finset.card_eq_sum_card_fiberwise hmap, hsum, Finset.sum_const, smul_eq_mul,
      Set.toFinset_card, ← Nat.card_eq_fintype_card]
  rw [hstep1, hstep2, hstep3, Nat.cast_mul]
  have hSne : (Nat.card S : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card, Nat.cast_ne_zero]
    exact Fintype.card_ne_zero
  rw [mul_comm ((Nat.card (MulAction.fixedBy I g) : ℂ)) ((Nat.card S : ℂ)),
    ← mul_assoc, inv_mul_cancel₀ hSne, one_mul]

/-! ## 4. Orbits and double transitivity -/

/-- The fixed points of `g` on `I × I` are the pairs of fixed points of `g` on `I`. -/
theorem card_fixedBy_prod (g : W) :
    Nat.card (MulAction.fixedBy (I × I) g) = Nat.card (MulAction.fixedBy I g) ^ 2 := by
  have hset : MulAction.fixedBy (I × I) g
      = (MulAction.fixedBy I g) ×ˢ (MulAction.fixedBy I g) := by
    ext p
    simp only [MulAction.mem_fixedBy, Set.mem_prod, Prod.smul_def, Prod.ext_iff]
  rw [hset, Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod, pow_two]

/-- **Burnside's lemma, squared.**  The sum of the squares of the numbers of fixed points of the
elements of `W` on `I` equals the number of `W`-orbits on `I × I` times `|W|`. -/
theorem sum_fixedBy_sq [Fintype W] :
    (∑ g : W, Nat.card (MulAction.fixedBy I g) ^ 2)
      = Nat.card (Quotient (MulAction.orbitRel W (I × I))) * Nat.card W := by
  classical
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group W (I × I)
  have hsum : (∑ g : W, Fintype.card ↑(MulAction.fixedBy (I × I) g))
      = ∑ g : W, Nat.card (MulAction.fixedBy I g) ^ 2 := by
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [← Nat.card_eq_fintype_card, card_fixedBy_prod]
  rw [hsum, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
  exact h

/-- **The self-inner product of the permutation character is the number of orbits on
`I × I`.** -/
theorem cfInner_permChar_eq_card_orbits [Fintype W]
    (htr : MulAction.IsPretransitive W I) (α : I) :
    Work.CharCore.cfInner
        (Work.Induction.indFun (MulAction.stabilizer W α)
          (fun _ : MulAction.stabilizer W α => (1 : ℂ)))
        (Work.Induction.indFun (MulAction.stabilizer W α)
          (fun _ : MulAction.stabilizer W α => (1 : ℂ)))
      = (Nat.card (Quotient (MulAction.orbitRel W (I × I))) : ℂ) := by
  classical
  have h1 : ∀ g : W, (Work.Induction.indFun (MulAction.stabilizer W α)
        (fun _ : MulAction.stabilizer W α => (1 : ℂ))) g
      = ((Nat.card (MulAction.fixedBy I g) : ℕ) : ℂ) :=
    fun g => indFun_triv_apply_eq_fixedBy htr α g
  have h2 : (∑ g : W, (Work.Induction.indFun (MulAction.stabilizer W α)
          (fun _ : MulAction.stabilizer W α => (1 : ℂ))) g
        * starRingEnd ℂ ((Work.Induction.indFun (MulAction.stabilizer W α)
          (fun _ : MulAction.stabilizer W α => (1 : ℂ))) g))
      = ((↑(∑ g : W, Nat.card (MulAction.fixedBy I g) ^ 2) : ℕ) : ℂ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [h1 g, Nat.cast_pow]
    simp only [map_natCast]
    ring
  rw [Work.CharCore.cfInner_apply, h2, sum_fixedBy_sq, Nat.cast_mul]
  have hW : (↑(Nat.card W) : ℂ) = (Fintype.card W : ℂ) := by rw [Nat.card_eq_fintype_card]
  rw [hW, mul_comm ((Nat.card (Quotient (MulAction.orbitRel W (I × I))) : ℂ))
      (Fintype.card W : ℂ), ← mul_assoc, inv_mul_cancel₀, one_mul]
  rw [Nat.cast_ne_zero]
  exact Fintype.card_ne_zero

/-- **Isaacs (5.17)**, converse direction: a transitive permutation group with exactly two orbits
on ordered pairs is doubly transitive. -/
theorem twoTransitive_of_card_orbits_eq_two
    (h : Nat.card (Quotient (MulAction.orbitRel W (I × I))) = 2) :
    MulAction.IsMultiplyPretransitive W I 2 := by
  classical
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  rw [Nat.card_eq_two_iff] at h
  obtain ⟨x, y, hxy, hcover⟩ := h
  have hcase : ∀ p : I × I,
      Quotient.mk (MulAction.orbitRel W (I × I)) p = x ∨
        Quotient.mk (MulAction.orbitRel W (I × I)) p = y := fun p => by
    have hmem : Quotient.mk (MulAction.orbitRel W (I × I)) p ∈ ({x, y} : Set _) := by
      rw [hcover]; exact Set.mem_univ _
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hne : ∀ (u v : I), u ≠ v →
      Quotient.mk (MulAction.orbitRel W (I × I)) (u, v) ≠
        Quotient.mk (MulAction.orbitRel W (I × I)) (u, u) := by
    intro u v huv hcontra
    have hrel : (u, v) ∈ MulAction.orbit W (u, u) :=
      MulAction.orbitRel_apply.mp (Quotient.exact hcontra)
    rw [MulAction.mem_orbit_iff] at hrel
    obtain ⟨g, hg⟩ := hrel
    rw [Prod.smul_mk] at hg
    exact huv ((congrArg Prod.fst hg).symm.trans (congrArg Prod.snd hg))
  -- ### every diagonal pair lies in the same class
  have hdiag : ∀ i : I, Quotient.mk (MulAction.orbitRel W (I × I)) (i, i)
      = Quotient.mk (MulAction.orbitRel W (I × I)) (a, a) := by
    intro i
    by_contra hne'
    have hne_ab_i : Quotient.mk (MulAction.orbitRel W (I × I)) (a, b) ≠
        Quotient.mk (MulAction.orbitRel W (I × I)) (i, i) := by
      intro hcon
      have hrel : (a, b) ∈ MulAction.orbit W (i, i) :=
        MulAction.orbitRel_apply.mp (Quotient.exact hcon)
      rw [MulAction.mem_orbit_iff] at hrel
      obtain ⟨g, hg⟩ := hrel
      rw [Prod.smul_mk] at hg
      exact hab ((congrArg Prod.fst hg).symm.trans (congrArg Prod.snd hg))
    have hab_a : Quotient.mk (MulAction.orbitRel W (I × I)) (a, b) ≠
        Quotient.mk (MulAction.orbitRel W (I × I)) (a, a) := hne a b hab
    rcases hcase (a, b) with h | h <;> rcases hcase (i, i) with hi | hi <;>
      rcases hcase (a, a) with ha | ha <;> simp_all [hxy]
  -- ### the two off-diagonal pairs lie in the same class
  have hcd_ab : Quotient.mk (MulAction.orbitRel W (I × I)) (c, d)
      = Quotient.mk (MulAction.orbitRel W (I × I)) (a, b) := by
    by_contra hne'
    have hcd_cd : Quotient.mk (MulAction.orbitRel W (I × I)) (c, d) ≠
        Quotient.mk (MulAction.orbitRel W (I × I)) (a, a) := by
      rw [← hdiag c]; exact hne c d hcd
    have hab_a : Quotient.mk (MulAction.orbitRel W (I × I)) (a, b) ≠
        Quotient.mk (MulAction.orbitRel W (I × I)) (a, a) := hne a b hab
    rcases hcase (a, b) with h | h <;> rcases hcase (c, d) with hi | hi <;>
      rcases hcase (a, a) with ha | ha <;> simp_all [hxy]
  have hrel : (c, d) ∈ MulAction.orbit W (a, b) :=
    MulAction.orbitRel_apply.mp (Quotient.exact hcd_ab)
  rw [MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  rw [Prod.smul_mk] at hg
  exact ⟨g, (Prod.ext_iff.mp hg).1, (Prod.ext_iff.mp hg).2⟩

/-- **Isaacs (5.17)**, the form used in Peterfalvi App. VI. -/
theorem twoTransitive_of_cfInner_permChar_eq_two [Fintype W]
    (htr : MulAction.IsPretransitive W I) (α : I)
    (h : Work.CharCore.cfInner
        (Work.Induction.indFun (MulAction.stabilizer W α)
          (fun _ : MulAction.stabilizer W α => (1 : ℂ)))
        (Work.Induction.indFun (MulAction.stabilizer W α)
          (fun _ : MulAction.stabilizer W α => (1 : ℂ))) = 2) :
    MulAction.IsMultiplyPretransitive W I 2 := by
  refine twoTransitive_of_card_orbits_eq_two ?_
  have h2 := cfInner_permChar_eq_card_orbits (W := W) (I := I) htr α
  rw [h2] at h
  exact Nat.cast_injective h


/-! ## 5. Auxiliary character-theoretic lemmas -/

/-- **The degree of an irreducible character is the sum of the multiplicities of the irreducible
characters of a (commutative) subgroup in its restriction.** -/
theorem sum_cfInner_resFun_eq_deg {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    [IsMulCommutative H] {ψ : G → ℂ} (hψ : ψ ∈ Work.CharCore.Irr G) :
    ((Work.CharCore.irrDeg ψ : ℂ))
      = ∑ μ ∈ Work.CharCore.Irr ↥H,
          Work.CharCore.cfInner (Work.Induction.resFun H ψ) μ := by
  have hc : Work.CharCore.IsClassFun (Work.Induction.resFun H ψ) :=
    Work.Induction.isClassFun_resFun (Work.CharCore.isClassFun_of_mem_Irr hψ)
  have h := congrFun (Work.CharCore.classFun_eq_sum_irr (G := ↥H) hc) 1
  rw [Finset.sum_apply] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [Work.Induction.resFun_apply] at h
  have hgoal : ψ (1 : G) = ∑ μ ∈ Work.CharCore.Irr ↥H,
      Work.CharCore.cfInner (Work.Induction.resFun H ψ) μ := by
    rw [show (1 : G) = ((1 : ↥H) : G) from rfl, h]
    refine Finset.sum_congr rfl (fun μ hμ => ?_)
    rw [Work.CharCore.irrDeg_spec hμ, Work.CharCore.irrDeg_eq_one_of_commutative hμ]
    simp
  rw [← Work.CharCore.irrDeg_spec hψ]
  exact hgoal

/-! ## 7. A universe-polymorphic copy of the exceptional-character machinery

The workspace's `Work.ZassenhausPSL2.exc_char_coherent` (Isaacs 7.18 for an abelian T.I.F.N.
subgroup) is stated for groups in `Type 0` only, while the main theorem here is stated for groups
in an arbitrary universe.  The lemmas below are verbatim copies of
`Submission.Work.ZassenhausPSL2.ZData.ExcCharSetup` and
`Submission.Work.ZassenhausPSL2.exc_char_coherent` with `Type` replaced by `Type*`; the two
`Submission.Blueprint` definitions they use (`excludingKernel`, `indLinear`, both restricted to
`Type 0`) are redefined here as `excludingKernelP` and `indLinearP`. -/

/-- `cfInner` does not depend on the chosen `Fintype` instance. -/
theorem cfInner_fintype_indep {α : Type*} (i₁ i₂ : Fintype α) (f g : α → ℂ) :
    @Work.Coherence.cfInner α i₁ f g = @Work.Coherence.cfInner α i₂ f g := by
  have huniv : (@Finset.univ α i₁) = (@Finset.univ α i₂) := by
    apply Finset.ext
    intro x
    simp
  have hcard : (@Fintype.card α i₁ : ℂ) = (@Fintype.card α i₂ : ℂ) := by
    rw [show @Fintype.card α i₁ = @Fintype.card α i₂ from by
      show (@Finset.univ α i₁).card = (@Finset.univ α i₂).card
      rw [huniv]]
  simp only [Work.Coherence.cfInner]
  rw [hcard, Finset.sum_congr huniv (fun x _ => rfl)]

/-- `Ind_H^G` as a `ℤ`-linear map on class functions (universe-polymorphic copy of
`Submission.Blueprint.indLinear`). -/
noncomputable def indLinearP {G : Type*} [Group G] [Fintype G] (H : Subgroup G) :
    (H → ℂ) →ₗ[ℤ] (G → ℂ) where
  toFun := Work.Induction.indFun H
  map_add' := Work.Induction.indFun_add H
  map_smul' := fun n φ => by
    simp only [RingHom.id_apply]
    rw [← Int.cast_smul_eq_zsmul ℂ n φ, Work.Induction.indFun_smul, Int.cast_smul_eq_zsmul]

/-- `{χ ∈ Irr H | Q₁ ⊄ ker χ}` (universe-polymorphic copy of
`Submission.Blueprint.excludingKernel`). -/
noncomputable def excludingKernelP {G : Type*} [Group G] [Fintype G] (H Q₁ : Subgroup G) :
    Finset (H → ℂ) :=
  (Work.CharCore.Irr H).filter (fun χ => ∃ x : H, (x : G) ∈ Q₁ ∧ χ x ≠ χ 1)


/-!
# Set-up for the T.I.F.N. exceptional-character lemma

Vocabulary and elementary group-theoretic facts for the proof of
`Work.ZassenhausPSL2.exc_char_coherent`: `K` is an abelian T.I.F.N. subgroup of a finite group `W`
(a T.I. set with `C_W(k) ≤ K` for `1 ≠ k ∈ K`), `N = N_W(K)`, and `𝒮 = {χ ∈ Irr N | K ⊄ ker χ}`.

The main statements are

* `Work.ZassenhausPSL2.centralizer_eq` — `C_W(k) = K` for `1 ≠ k ∈ K`;
* `Work.ZassenhausPSL2.isTISet` — `K \ {1}` is a TI set with normalizer `N` in the sense of
  Dade (`Work.BrauerSuzuki.IsTISet`);
* `mem_scriptS` — membership in `𝒮`.

**Instances.** `excludingKernelP` builds the `Fintype` instance of the
subgroup it works with from the *ambient* `Fintype`; to keep statement and goal in sync, the
lemmas below are stated with `[Fintype W]` only and let instance search derive the subgroup
instances.
-/





variable {W : Type*} [Group W] [Fintype W]

/-- The normalizer `N_W(K)`. -/
abbrev nrm (K : Subgroup W) : Subgroup W := Subgroup.normalizer (K : Set W)

/-- `K` viewed as a subgroup of `N_W(K)`. -/
abbrev Kn (K : Subgroup W) : Subgroup ↥(nrm K) := K.subgroupOf (nrm K)

/-- Peterfalvi's set `𝒮 = {χ ∈ Irr N_W(K) | K ⊄ ker χ}` (the characters of the normalizer of
`K` that do not contain `K` in their kernel). -/
noncomputable abbrev scriptS (K : Subgroup W) : Finset (↥(nrm K) → ℂ) :=
  excludingKernelP (nrm K) K

/-- `Ind_{N_W(K)}^W` as a `ℤ`-linear map on class functions. -/
noncomputable abbrev indLinK (K : Subgroup W) : (↥(nrm K) → ℂ) →ₗ[ℤ] (W → ℂ) :=
  indLinearP (nrm K)

/-- **The canonical `Fintype` instance on `↥(N_W K)`**, the one instance search produces from the
ambient `Fintype W` (and hence the one used internally by
`excludingKernelP`).  Keeping a *named* copy lets a proof work at this
instance even in a context where another instance for `↥(N_W K)` is in scope. -/
noncomputable def instNrm (K : Subgroup W) : Fintype ↥(nrm K) := inferInstance

variable (K : Subgroup W)

/-- `K ≤ N_W(K)`. -/
lemma le_nrm : K ≤ nrm K := Subgroup.le_normalizer

/-- `K` is normal in `N_W(K)`. -/
lemma kn_normal (K : Subgroup W) : (Kn K).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (le_nrm K)).mpr le_rfl

/-- `K` is normal in `N_W(K)`, as an instance. -/
instance (K : Subgroup W) : (Kn K).Normal := kn_normal K

/-- **`C_W(k) = K` for `1 ≠ k ∈ K`.**  This is the "F" of T.I.F.N.: every non-identity element
of `K` is self-centralising (the hypothesis `hcent` gives `≤`, and commutativity of `K` gives
`≥`). -/
lemma centralizer_eq (hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K)
    {k : W} (hk : k ∈ K) (hk1 : k ≠ 1) : Subgroup.centralizer ({k} : Set W) = K := by
  refine le_antisymm (hcent k hk hk1) ?_
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hKcomm y hy k hk

/-- Membership in `𝒮`. -/
lemma mem_scriptS {χ : ↥(nrm K) → ℂ} :
    χ ∈ scriptS K ↔
      χ ∈ Work.CharCore.Irr ↥(nrm K) ∧
        ∃ x : ↥(nrm K), (x : W) ∈ K ∧ χ x ≠ χ 1 := by
  exact Finset.mem_filter (s := Work.CharCore.Irr ↥(nrm K)) (a := χ)
    (p := fun (ψ : ↥(nrm K) → ℂ) => ∃ x : ↥(nrm K), (x : W) ∈ K ∧ ψ x ≠ ψ 1)

/-- `𝒮 ⊆ Irr N`. -/
lemma scriptS_subset_Irr : ↑(scriptS K) ⊆ Work.CharCore.Irr ↥(nrm K) := by
  intro χ hχ
  exact ((mem_scriptS K).mp hχ).1

/-- **`K \ {1}` is a TI set with normalizer `N_W(K)`** (Dade's set form), for a TI subgroup `K`
with `C_W(k) ≤ K` for `1 ≠ k ∈ K`. -/
lemma isTISet (hTI : ∀ g : W, g ∉ nrm K → K ⊓ Submission.Blueprint.conj g K = ⊥)
    (hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K) :
    Work.BrauerSuzuki.IsTISet ((K : Set W) \ {1}) (nrm K) where
  one_notMem := by simp
  subset := by
    intro x hx
    exact le_nrm K (by simpa using hx.1)
  inv_mem := by
    rintro x ⟨hxK, hx1⟩
    refine ⟨K.inv_mem hxK, ?_⟩
    simp only [Set.mem_singleton_iff] at hx1 ⊢
    exact inv_ne_one.mpr hx1
  mem_normalizer := by
    rintro h hh x ⟨hxK, hx1⟩
    have hconj : h * x * h⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hh x).mp hxK
    refine ⟨hconj, ?_⟩
    simp only [Set.mem_singleton_iff] at hx1 ⊢
    intro hc
    exact hx1 (by
      calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
        _ = 1 := by rw [hc]; group)
  normalizer_le := by
    rintro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      by_cases h1 : h = 1
      · subst h1; simp
      · exact (hg ⟨hh, by simpa [Set.mem_singleton_iff] using h1⟩).1
    · intro hh
      by_cases h1 : h = 1
      · simpa [h1] using K.one_mem
      · have hψ_exists : ∀ x : ↥K, (if (x : W) = 1 then 1 else g * (x : W) * g⁻¹) ∈ K := by
          intro x
          by_cases hx : (x : W) = 1
          · simp [hx]
          · simp only [hx, if_false]
            exact (hg ⟨x.2, by simpa [Set.mem_singleton_iff] using hx⟩).1
        let ψ : ↥K → ↥K := fun x => ⟨_, hψ_exists x⟩
        have hψ_val : ∀ x : ↥K, ((ψ x : ↥K) : W) = g * (x : W) * g⁻¹ := by
          intro x
          by_cases hx : (x : W) = 1
          · dsimp only [ψ]
            rw [if_pos hx, hx]
            group
          · dsimp only [ψ]
            rw [if_neg hx]
        have hinj : Function.Injective ψ := by
          intro x y hxy
          have hv : g * (x : W) * g⁻¹ = g * (y : W) * g⁻¹ := by
            rw [← hψ_val x, ← hψ_val y, hxy]
          exact Subtype.ext (by
            have hc := congrArg (fun z => g⁻¹ * z * g) hv
            simpa [mul_assoc] using hc)
        have hsurj : Function.Surjective ψ := (Finite.injective_iff_surjective).mp hinj
        obtain ⟨x, hx⟩ := hsurj ⟨g * h * g⁻¹, hh⟩
        have hxval : g * (x : W) * g⁻¹ = g * h * g⁻¹ := by
          rw [← hψ_val x, hx]
        have hxh : (x : W) = h := by
          have hc := congrArg (fun z => g⁻¹ * z * g) hxval
          simpa [mul_assoc] using hc
        rw [← hxh]; exact x.2
  conj_disjoint := by
    rintro g hg x y ⟨hxK, hx1⟩ ⟨hyK, hy1⟩ hconj
    -- `x = g⁻¹ y g ∈ K ⊓ g⁻¹ K g`, and `g⁻¹ ∉ N_W(K)`
    have hginv : g⁻¹ ∉ nrm K := fun h => hg (by simpa using (nrm K).inv_mem h)
    have hxmem : x ∈ K ⊓ Submission.Blueprint.conj g⁻¹ K := by
      refine ⟨hxK, ?_⟩
      rw [Submission.Blueprint.conj]
      refine Subgroup.mem_map.mpr ⟨y, hyK, ?_⟩
      change (MulAut.conj g⁻¹) y = x
      rw [MulAut.conj_apply]
      rw [← hconj]; group
    rw [hTI g⁻¹ hginv, Subgroup.mem_bot] at hxmem
    exact hx1 (by simpa [Set.mem_singleton_iff] using hxmem)




/-!
# The exceptional characters of an abelian T.I.F.N. subgroup are coherent

`Work.ZassenhausPSL2.exc_char_coherent` (Isaacs, *Character Theory of Finite Groups*,
Corollary 7.18(a),(b), i.e. the abelian case of the Feit–Sibley exceptional-character theorem):
if `K` is an abelian T.I.F.N. subgroup of the finite group `W` — a T.I. subgroup with
`C_W(k) ≤ K` for `1 ≠ k ∈ K` — then the set `𝒮 = {χ ∈ Irr N_W(K) | K ⊄ ker χ}` is coherent for
induction `Ind_{N_W(K)}^W`.

The proof follows Feit/Isaacs:

* every `χ ∈ 𝒮` is induced from a non-principal character of `K` (`scriptS_eq_induced`), hence
  has degree `[N_W(K) : K]` (`scriptS_degree`) and vanishes off `K` (`scriptS_vanish`);
* the Dade/Brauer–Suzuki isometry `⟨α^W, β^W⟩ = ⟨α, β⟩` on `ℤ[𝒮]⁰` (`isometryOn_scriptS`), from
  the TI-set form `Work.BrauerSuzuki.TI.cfInner_indFun_eq_of_TISet`;
* `(χ - x₀)^W` is a virtual character of degree zero (`isVChar_indLin_sub`), so
  `Work.Coherence.coherent_of_norm_two_lift` (FT Lemma 10.1 / Isaacs Corollary 7.15) applies as
  soon as `|𝒮| ≥ 2`; the remaining case `|𝒮| ≤ 1` is `coherent_of_card_le_one`.
-/




variable {W : Type*} [Group W] [Fintype W]

/-! ## Orthonormality of `𝒮` -/

/-- `𝒮` is an orthonormal set: it consists of irreducible characters. -/
lemma orthonormal_scriptS (K : Subgroup W) : Work.Coherence.Orthonormal (scriptS K) :=
  Work.Coherence.Orthonormal.mono Work.CharCore.Orthonormal_Irr (scriptS_subset_Irr K)

/-! ## The structure of `𝒮`: every member is induced from `K` -/

/-- **The inertia group of a non-principal character of `K` in `N_W(K)` is `K`.**

If `g ∈ N_W(K)` fixes `θ ∈ Irr K` (viewed inside `N_W(K)`), then either `g ∈ K` or `θ = 1`:
if `g ∉ K` then conjugation by `g` is a fixed-point-free automorphism of `K` (a fixed `k ≠ 1`
would give `g ∈ C_W(k) ≤ K`), and a fixed-point-free automorphism has no non-trivial invariant
irreducible character (`Work.Frobenius.Induced.conjChar_ne_self_of_fpf`). -/
lemma inertia_eq (K : Subgroup W)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K)
    {θ : ↥(Kn K) → ℂ} (hθ : θ ∈ Work.CharCore.Irr ↥(Kn K)) (hθ1 : θ ≠ 1) :
    Work.Clifford.inertia (Kn K) θ = Kn K := by
  have hθCl : θ ∈ Work.Clifford.Irr ↥(Kn K) := (Work.Clifford.mem_Irr_charCore_iff).mpr hθ
  have hθF : θ ∈ Work.Frobenius.Irr ↥(Kn K) :=
    (Work.Frobenius.Bridge.mem_Irr_iff_coherence).mpr
      ((Work.Clifford.mem_Irr_iff_coherence (G := ↥(Kn K))).mp hθCl)
  refine le_antisymm ?_ (Work.Clifford.le_inertia_of_mem_Irr hθCl)
  intro g hg
  rw [Work.Clifford.mem_inertia] at hg
  by_contra hgK
  -- conjugation by `g` is fixed-point-free on `Kn K`
  have hfpf : ∀ k : ↥(nrm K), k ∈ Kn K → g * k * g⁻¹ = k → k = 1 := by
    intro k hk hkeq
    by_contra hk1
    have hkW : (k : W) ∈ K := (Subgroup.mem_subgroupOf).mp hk
    have hkne : (k : W) ≠ 1 := fun h => hk1 (Subtype.ext h)
    have hmem : (g : W) ∈ Subgroup.centralizer ({(k : W)} : Set W) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : (g : W) * (k : W) * (g : W)⁻¹ = (k : W) :=
        congrArg (fun z : ↥(nrm K) => (z : W)) hkeq
      calc (g : W) * (k : W) = ((g : W) * (k : W) * (g : W)⁻¹) * (g : W) := by group
        _ = (k : W) * (g : W) := by rw [h1]
    exact hgK (hcent (k : W) hkW hkne hmem)
  have hne := Work.Frobenius.Induced.conjChar_ne_self_of_fpf
    (G := ↥(nrm K)) (K := Kn K) hθF hθ1 hfpf
  rw [Work.Frobenius.Induced.conjChar_eq_conjFun] at hne
  exact hne hg

/-- **Induction of a non-principal character of the kernel is irreducible.**

For `θ ∈ Irr K` non-principal with `I_{N_W(K)}(θ) = K`, the induced function
`Ind_K^{N_W(K)} θ` is an irreducible character: its norm is `|I(θ)|/|K| = 1`
(`Work.Clifford.cfInner_indFun_normal'`), it is a virtual character
(`Work.Induction.isVChar_indFun`), and `Work.CharCore.vchar_norm_one` plus positivity of the
degree (`Work.Induction.indFun_apply_one`) identifies it. -/
lemma ind_irr (K : Subgroup W)
    {θ : ↥(Kn K) → ℂ} (hθ : θ ∈ Work.CharCore.Irr ↥(Kn K)) (hθ1 : θ ≠ 1)
    (hinertia : Work.Clifford.inertia (Kn K) θ = Kn K) :
    Work.Induction.indFun (Kn K) θ ∈ Work.CharCore.Irr ↥(nrm K) := by
  have hθCl : θ ∈ Work.Clifford.Irr ↥(Kn K) := (Work.Clifford.mem_Irr_charCore_iff).mpr hθ
  have hcard : (Nat.card ↥(Kn K) : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card, Nat.cast_ne_zero]; exact Fintype.card_ne_zero
  have hidx : ((Kn K).index : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Subgroup.index_ne_zero_of_finite (H := Kn K))
  have hnorm : Work.CharCore.cfInner (Work.Induction.indFun (Kn K) θ)
      (Work.Induction.indFun (Kn K) θ) = 1 := by
    rw [Work.Clifford.cfInner_indFun_normal' (N := Kn K) hθCl, hinertia]
    exact mul_inv_cancel₀ hcard
  have hV : Work.CharCore.IsVChar (Work.Induction.indFun (Kn K) θ) :=
    Work.Induction.isVChar_indFun (Work.CharCore.IsVChar.of_mem_Irr hθ)
  obtain ⟨χ, hχIrr, hcase⟩ := Work.CharCore.vchar_norm_one hV hnorm
  rcases hcase with h | h
  · rw [h]; exact hχIrr
  · exfalso
    have h1 : Work.Induction.indFun (Kn K) θ 1 = -χ 1 := by rw [h]; rfl
    rw [Work.Induction.indFun_apply_one, Work.CharCore.irrDeg_spec hθ,
      Work.CharCore.irrDeg_spec hχIrr] at h1
    have h2 : (((Kn K).index : ℝ) * (Work.CharCore.irrDeg θ : ℝ))
        = -((Work.CharCore.irrDeg χ : ℝ)) := by
      apply Complex.ofReal_injective
      push_cast
      exact h1
    have h4 : (0 : ℝ) < ((Kn K).index : ℝ) * (Work.CharCore.irrDeg θ : ℝ) :=
      mul_pos (Nat.cast_pos.mpr
        (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := Kn K))))
        (Work.CharCore.irrDeg_pos' hθ)
    have h5 : (0 : ℝ) < (Work.CharCore.irrDeg χ : ℝ) := Work.CharCore.irrDeg_pos' hχIrr
    linarith

/-- **The structure of `𝒮`.**  Every `χ ∈ 𝒮` is induced from a non-principal irreducible
character of `K`: `χ|_K` has a non-principal constituent `θ` (otherwise it would be constant and
`K` would lie in `ker χ`), its inertia group is `K` (`inertia_eq`), so `Ind_K^{N_W(K)} θ` is an
irreducible character (`ind_irr`) that pairs non-trivially with `χ` (Frobenius reciprocity), hence
equals `χ`. -/
lemma scriptS_eq_induced (K : Subgroup W)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K)
    {χ : ↥(nrm K) → ℂ} (hχ : χ ∈ scriptS K) :
    ∃ θ : ↥(Kn K) → ℂ, θ ∈ Work.CharCore.Irr ↥(Kn K) ∧ θ ≠ 1 ∧
      χ = Work.Induction.indFun (Kn K) θ := by
  obtain ⟨hχIrr, x₀, hx₀K, hx₀ne⟩ := (mem_scriptS K).mp hχ
  -- ### Step 1: `χ|_K` has a non-principal constituent
  have hstep1 : ∃ θ ∈ Work.CharCore.Irr ↥(Kn K), θ ≠ 1 ∧
      Work.CharCore.cfInner (Work.Clifford.resFun (Kn K) χ) θ ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ θ ∈ Work.CharCore.Irr ↥(Kn K), θ ≠ 1 →
        Work.CharCore.cfInner (Work.Clifford.resFun (Kn K) χ) θ = 0 := by
      intro θ hθ hθ1
      by_contra hne
      exact hcon ⟨θ, hθ, hθ1, hne⟩
    have hχcf : Work.CharCore.IsClassFun χ := Work.CharCore.isClassFun_of_mem_Irr hχIrr
    have hrescf : Work.CharCore.IsClassFun (Work.Clifford.resFun (Kn K) χ) := by
      intro a b
      exact hχcf a b
    have hsum := Work.CharCore.classFun_eq_sum_irr hrescf
    have hsingle : (∑ y ∈ Work.CharCore.Irr ↥(Kn K),
          (Work.CharCore.cfInner (Work.Clifford.resFun (Kn K) χ) y) • y)
        = (Work.CharCore.cfInner (Work.Clifford.resFun (Kn K) χ) 1) •
            (1 : ↥(Kn K) → ℂ) := by
      refine Finset.sum_eq_single (1 : ↥(Kn K) → ℂ) ?_ ?_
      · intro b hb hb1
        rw [hcon' b hb hb1, zero_smul]
      · intro hnot
        exact absurd (Work.CharCore.principalChar_mem_Irr (G := ↥(Kn K))) hnot
    have hcollapse : Work.Clifford.resFun (Kn K) χ =
        (Work.CharCore.cfInner (Work.Clifford.resFun (Kn K) χ) 1) • (1 : ↥(Kn K) → ℂ) :=
      hsum.trans hsingle
    have hval := congrFun hcollapse (⟨x₀, hx₀K⟩ : ↥(Kn K))
    have hval1 := congrFun hcollapse (1 : ↥(Kn K))
    simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at hval hval1
    exact hx₀ne (hval.trans hval1.symm)
  -- ### Step 2: `χ = Ind_K^{N_W(K)} θ`
  obtain ⟨θ, hθIrr, hθ1, hpair⟩ := hstep1
  have hIndIrr : Work.Induction.indFun (Kn K) θ ∈ Work.CharCore.Irr ↥(nrm K) :=
    ind_irr K hθIrr hθ1 (inertia_eq K hcent hθIrr hθ1)
  refine ⟨θ, hθIrr, hθ1, ?_⟩
  have hpair' : Work.CharCore.cfInner χ (Work.Induction.indFun (Kn K) θ) ≠ 0 := by
    intro hzero
    -- `⟨Ind θ, χ⟩ = ⟨θ, χ|_K⟩ = 0`
    have h2 : Work.CharCore.cfInner (Work.Induction.indFun (Kn K) θ) χ = 0 := by
      have hs := Work.CharCore.cfInner_conj_symm χ (Work.Induction.indFun (Kn K) θ)
      rw [hzero] at hs
      exact star_eq_zero.mp hs.symm
    have h3 : Work.CharCore.cfInner θ (Work.Clifford.resFun (Kn K) χ) = 0 := by
      have hrec := Work.Induction.frobenius_reciprocity (Kn K) θ χ
        (Work.CharCore.isClassFun_of_mem_Irr hχIrr)
      rw [h2] at hrec
      exact hrec.symm
    have h4 : Work.CharCore.cfInner (Work.Clifford.resFun (Kn K) χ) θ = 0 := by
      have hs := Work.CharCore.cfInner_conj_symm (Work.Clifford.resFun (Kn K) χ) θ
      rw [h3, map_zero] at hs
      exact hs
    exact hpair h4
  by_contra hne
  have horth := Work.CharCore.irr_orthonormal χ (Work.Induction.indFun (Kn K) θ) hχIrr hIndIrr
  rw [horth, ite_eq_right hne] at hpair'
  exact hpair' rfl

/-! ## Vanishing and degree of members of `𝒮` -/

/-- Members of `𝒮` vanish off `K` (they are induced from `K`). -/
lemma scriptS_vanish (K : Subgroup W)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K)
    {χ : ↥(nrm K) → ℂ} (hχ : χ ∈ scriptS K) {x : ↥(nrm K)} (hx : (x : W) ∉ K) :
    χ x = 0 := by
  obtain ⟨θ, -, -, hχeq⟩ := scriptS_eq_induced K hcent hχ
  rw [hχeq, Work.Induction.indFun_apply_def]
  rw [Finset.sum_eq_zero (fun y _ => ?_), mul_zero]
  by_cases hy : y * x * y⁻¹ ∈ Kn K
  · rw [dite_eq_left hy]
    exfalso
    apply hx
    have hmem : x ∈ Kn K := by
      have h := (inferInstance : (Kn K).Normal).conj_mem' (y * x * y⁻¹) hy y
      convert h using 1
      group
    exact (Subgroup.mem_subgroupOf).mp hmem
  · rw [dite_eq_right hy]

/-- Members of `ℤ[𝒮]` vanish off `K`. -/
lemma zSpan_scriptS_vanish (K : Subgroup W)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K)
    {α : ↥(nrm K) → ℂ} (hα : α ∈ Work.Coherence.ZSpan (scriptS K))
    {x : ↥(nrm K)} (hx : (x : W) ∉ K) : α x = 0 := by
  obtain ⟨c, rfl⟩ := hα
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_eq_zero fun y _ => by rw [scriptS_vanish K hcent y.2 hx, mul_zero]

/-- Members of `ℤ[𝒮]` are class functions. -/
lemma isClassFun_of_mem_zSpan_scriptS (K : Subgroup W)
    {α : ↥(nrm K) → ℂ} (hα : α ∈ Work.Coherence.ZSpan (scriptS K)) :
    Work.CharCore.IsClassFun α := by
  obtain ⟨c, rfl⟩ := hα
  refine Work.CharCore.IsClassFun.sum _ _ (fun x _ => ?_)
  exact Work.CharCore.IsClassFun.smul _
    (Work.CharCore.isClassFun_of_mem_Irr ((mem_scriptS K).mp x.2).1)

/-- Every member of `𝒮` has degree `[N_W(K) : K]`. -/
lemma scriptS_degree (K : Subgroup W)
    (hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K)
    {χ : ↥(nrm K) → ℂ} (hχ : χ ∈ scriptS K) : χ 1 = ((Kn K).index : ℂ) := by
  obtain ⟨θ, hθIrr, -, hχeq⟩ := scriptS_eq_induced K hcent hχ
  haveI : IsMulCommutative ↥(Kn K) :=
    isMulCommutative_iff.mpr (fun (a b : ↥(Kn K)) =>
      Subtype.ext (Subtype.ext (hKcomm (a : W) a.2 (b : W) b.2)))
  rw [hχeq, Work.Induction.indFun_apply_one, Work.CharCore.irrDeg_spec hθIrr,
    Work.CharCore.irrDeg_eq_one_of_commutative hθIrr, Nat.cast_one, mul_one]

/-! ## The Brauer–Suzuki isometry -/

/-- **The Dade/Brauer–Suzuki isometry** `⟨α^W, β^W⟩_W = ⟨α, β⟩_N` for `α, β ∈ ℤ[𝒮]⁰`, where
`N = N_W(K)`: elements of `ℤ[𝒮]⁰` are class functions supported in `K \ {1}`, so the general
TI-set isometry applies to the TI set `K \ {1}` with normalizer `N`. -/
lemma isometryOn_scriptS (K : Subgroup W)
    (hTI : ∀ g : W, g ∉ nrm K → K ⊓ Submission.Blueprint.conj g K = ⊥)
    (hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K) :
    Work.Coherence.IsometryOn (scriptS K) (indLinK K) := by
  refine ⟨fun α hα β hβ => ?_⟩
  have hα' := (Work.Coherence.mem_zSpan0).mp hα
  have hβ' := (Work.Coherence.mem_zSpan0).mp hβ
  have hαsup : Work.BrauerSuzuki.SupportLeSub α ((K : Set W) \ {1}) := by
    intro x hx
    by_cases hxK : (x : W) ∈ K
    · have hx1 : x = 1 := by
        refine Subtype.ext ?_
        by_contra hne
        exact hx ⟨hxK, by simpa [Set.mem_singleton_iff] using hne⟩
      rw [hx1]; exact hα'.2
    · exact zSpan_scriptS_vanish K hcent hα'.1 hxK
  have hβsup : Work.BrauerSuzuki.SupportLeSub β ((K : Set W) \ {1}) := by
    intro x hx
    by_cases hxK : (x : W) ∈ K
    · have hx1 : x = 1 := by
        refine Subtype.ext ?_
        by_contra hne
        exact hx ⟨hxK, by simpa [Set.mem_singleton_iff] using hne⟩
      rw [hx1]; exact hβ'.2
    · exact zSpan_scriptS_vanish K hcent hβ'.1 hxK
  exact Work.BrauerSuzuki.TI.cfInner_indFun_eq_of_TISet (isTISet K hTI hKcomm hcent)
    (isClassFun_of_mem_zSpan_scriptS K hα'.1) (isClassFun_of_mem_zSpan_scriptS K hβ'.1)
    hαsup hβsup

/-! ## The virtual character `(χ - x₀)^W` -/

/-- `(χ - x₀)^W` is a virtual character (a difference of two induced genuine characters). -/
lemma isVChar_indLin_sub (K : Subgroup W) {χ x₀ : ↥(nrm K) → ℂ}
    (hχ : χ ∈ scriptS K) (hx₀ : x₀ ∈ scriptS K) :
    Work.Coherence.IsVChar (indLinK K (χ - x₀)) := by
  rw [map_sub]
  refine (Work.CharCore.IsVChar_iff_coherence _).mp (Work.CharCore.IsVChar.sub ?_ ?_)
  · exact Work.Induction.isVChar_indFun
      (Work.CharCore.IsVChar.of_mem_Irr ((mem_scriptS K).mp hχ).1)
  · exact Work.Induction.isVChar_indFun
      (Work.CharCore.IsVChar.of_mem_Irr ((mem_scriptS K).mp hx₀).1)

/-- `(χ - x₀)^W` has degree zero. -/
lemma indLin_sub_apply_one (K : Subgroup W) (χ x₀ : ↥(nrm K) → ℂ) :
    (indLinK K (χ - x₀)) 1 = ((nrm K).index : ℂ) * ((χ - x₀) 1) := by
  change Work.Induction.indFun (nrm K) (χ - x₀) 1 = ((nrm K).index : ℂ) * ((χ - x₀) 1)
  rw [Work.Induction.indFun_apply_one]

/-! ## The case `|𝒮| ≤ 1` -/

/-- **Coherence is trivial for sets of at most one irreducible character.**  If `S ⊆ Irr H` and
`S.card ≤ 1`, then `ZSpan0 S = 0` (there is at most one summand, of non-zero degree), so the
isometry condition on `ℤ[S]⁰` is vacuous and the lift `φ x = 1_G` (the constant function, a virtual
character, with `⟨1_G, 1_G⟩ = 1`) satisfies the extension lemma
`Work.Coherence.coherent_of_isometry_extension`. -/
lemma coherent_of_card_le_one {H G : Type*} [Group H] [Fintype H] [Group G] [Fintype G]
    {S : Finset (H → ℂ)} (τ : (H → ℂ) →ₗ[ℤ] (G → ℂ))
    (hS : ↑S ⊆ Work.Coherence.Irr H) (hdeg : ∀ x ∈ S, x 1 ≠ 0) (hcard : S.card ≤ 1) :
    Work.Coherence.Coherent S τ := by
  rcases Finset.eq_empty_or_nonempty S with h0 | ⟨χ, hχmem⟩
  · rw [h0]; exact Work.Coherence.coherent_empty
  · have huniq : S = {χ} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hχmem, fun y hy => ?_⟩
      by_contra hne
      have h2 : 2 ≤ S.card := by
        have hsub : ({χ, y} : Finset (H → ℂ)) ⊆ S := by
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        calc (2 : ℕ) = ({χ, y} : Finset (H → ℂ)).card :=
              (Finset.card_pair (a := χ) (b := y) (Ne.symm hne)).symm
          _ ≤ S.card := Finset.card_le_card hsub
      omega
    subst huniq
    have hχirr : χ ∈ Work.Coherence.Irr H := hS (by simp)
    have hχ1 : χ 1 ≠ 0 := hdeg χ (by simp)
    have hSorth : Work.Coherence.Orthonormal ({χ} : Finset (H → ℂ)) :=
      Work.Coherence.irr_orthonormal_finset (fun z hz => hS (by simpa using hz))
    -- `ℤ[{χ}]⁰ = 0`
    have hzero : ∀ α ∈ Work.Coherence.ZSpan0 ({χ} : Finset (H → ℂ)), α = 0 := by
      intro α hα
      obtain ⟨hc, hα1⟩ := (Work.Coherence.mem_zSpan0).mp hα
      obtain ⟨c, hc'⟩ := (Work.Coherence.mem_zSpan).mp hc
      have hsum_eq : (∑ x : ↥({χ} : Finset (H → ℂ)),
            (c x : ℂ) • ((x : ↥({χ} : Finset (H → ℂ))) : H → ℂ))
          = (c ⟨χ, Finset.mem_singleton_self χ⟩ : ℂ) • χ := by
        refine Finset.sum_eq_single (⟨χ, Finset.mem_singleton_self χ⟩ :
          ↥({χ} : Finset (H → ℂ))) ?_ ?_
        · intro b _ hb
          exact absurd (Subsingleton.elim b _) hb
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      have hval : (c ⟨χ, Finset.mem_singleton_self χ⟩ : ℂ) = 0 := by
        have h := congrFun (hc'.trans hsum_eq) 1
        rw [hα1, Pi.smul_apply, smul_eq_mul] at h
        rcases mul_eq_zero.mp h.symm with h' | h'
        · exact h'
        · exact absurd h' hχ1
      rw [hc', hsum_eq, hval, zero_smul]
    refine Work.Coherence.coherent_of_isometry_extension (x₀ := χ) hSorth (by simp)
      (fun x hx => by rw [Finset.mem_singleton.mp hx]) hχ1 ?_
      (φ := fun _ => (1 : G → ℂ)) ?_ ?_ ?_
    · refine ⟨fun α hα β hβ => ?_⟩
      rw [hzero α hα, hzero β hβ]
      simp
    · intro x hx
      rw [Finset.mem_singleton.mp hx]
      have h1 : Work.Coherence.cfInner (1 : G → ℂ) (1 : G → ℂ) = 1 := by
        rw [Work.Coherence.cfInner_apply]
        simp
      have h2 : Work.Coherence.cfInner χ χ = 1 := by
        rw [Work.Coherence.irr_cfInner hχirr hχirr]; simp
      rw [h1, h2]
    · intro x hx
      rw [Finset.mem_singleton.mp hx]
    · intro x hx
      refine (Work.CharCore.IsVChar_iff_coherence _).mp
        (Work.CharCore.IsVChar.of_mem_Irr (Work.CharCore.principalChar_mem_Irr))

/-! ## Instance transfer

`Work.Coherence.Coherent` depends on the chosen `Fintype` instance on the subgroup only through
`cfInner`, which is instance-independent (`cfInner_fintype_indep`).  This
lets us move a coherence statement between different instances. -/

/-- `IsometryOnAll` is insensitive to the chosen `Fintype` instances. -/
theorem isometryOnAll_fintype_indep {H G : Type*} [Group H]
    {i j : Fintype H} {iG jG : Fintype G}
    {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (h : @Work.Coherence.IsometryOnAll G H i iG S τ) :
    @Work.Coherence.IsometryOnAll G H j jG S τ := by
  obtain ⟨h2⟩ := h
  exact ⟨fun α hα β hβ => by
    calc @Work.Coherence.cfInner G jG (τ α) (τ β)
        = @Work.Coherence.cfInner G iG (τ α) (τ β) :=
          cfInner_fintype_indep jG iG (τ α) (τ β)
      _ = @Work.Coherence.cfInner H i α β := h2 α hα β hβ
      _ = @Work.Coherence.cfInner H j α β :=
          (cfInner_fintype_indep j i α β).symm⟩

/-- `Coherent` is insensitive to the chosen `Fintype` instances. -/
theorem coherent_fintype_indep {H G : Type*} [Group H] [Group G]
    (iH jH : Fintype H) (iG jG : Fintype G)
    {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (h : @Work.Coherence.Coherent G H _ iH _ iG S τ) :
    @Work.Coherence.Coherent G H _ jH _ jG S τ := by
  obtain ⟨τ', h1, h2, h3⟩ := h
  exact ⟨τ', h1, isometryOnAll_fintype_indep h2, h3⟩

/-! ## The main theorem -/

theorem exc_char_coherent {W : Type*} [Group W] [Fintype W] (K : Subgroup W) [Fintype ↥K]
    [Fintype ↥(Subgroup.normalizer (K : Set W))]
    (hTI : ∀ g : W, g ∉ Subgroup.normalizer (K : Set W) →
      K ⊓ Submission.Blueprint.conj g K = ⊥)
    (hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K) :
    Work.Coherence.Coherent
      (excludingKernelP (Subgroup.normalizer (K : Set W)) K)
      (indLinearP (Subgroup.normalizer (K : Set W))) := by
  -- work with the canonical `Fintype` instance on `N_W(K)` throughout
  letI : Fintype ↥(nrm K) := instNrm K
  have main : Work.Coherence.Coherent (scriptS K) (indLinK K) := by
    by_cases hcard : 2 ≤ (scriptS K).card
    · obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp (by omega : 0 < (scriptS K).card)
      have hdeg : ∀ x ∈ scriptS K, x 1 = x₀ 1 := fun x hx =>
        (scriptS_degree K hKcomm hcent hx).trans (scriptS_degree K hKcomm hcent hx₀).symm
      have hx₀1 : x₀ 1 ≠ 0 := by
        rw [scriptS_degree K hKcomm hcent hx₀]
        exact_mod_cast Subgroup.index_ne_zero_of_finite (H := Kn K)
      refine Work.Coherence.coherent_of_norm_two_lift (orthonormal_scriptS K) hx₀ hdeg hx₀1
        (isometryOn_scriptS K hTI hKcomm hcent) (fun x hx => isVChar_indLin_sub K hx hx₀)
        (fun x hx => ?_) hcard
      rw [indLin_sub_apply_one K x x₀, Pi.sub_apply, hdeg x hx, sub_self, mul_zero]
    · refine coherent_of_card_le_one (indLinK K) ?_ ?_ (by omega)
      · intro x hx
        exact (Work.CharCore.mem_Irr_iff_coherence).mp ((mem_scriptS K).mp hx).1
      · intro x hx
        rw [scriptS_degree K hKcomm hcent hx]
        exact_mod_cast Subgroup.index_ne_zero_of_finite (H := Kn K)
  exact coherent_fintype_indep (instNrm K) _ _ _ main




/-- **The number of exceptional characters.**  For an abelian T.I.F.N. subgroup `K` of `W`, the
number of irreducible characters of `N_W(K)` that do not contain `K` in their kernel, multiplied
by the index `[N_W(K) : K]`, is `|K| - 1`. -/
theorem scriptS_card_mul_index {W : Type*} [Group W] [Fintype W] {K : Subgroup W}
    (hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K) :
    (scriptS K).card * (Kn K).index
      = Nat.card ↥K - 1 := by
  classical
  have hHK : Nat.card ↥(Kn K) = Nat.card ↥K :=
    Nat.card_congr
      { toFun := fun x => ⟨(x : W), x.2⟩
        invFun := fun k => ⟨⟨(k : W), le_nrm K k.2⟩, k.2⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun k => Subtype.ext rfl }
  have hcardN : Nat.card ↥(nrm K)
      = Nat.card ↥K * (Kn K).index := by
    rw [← hHK, ← Subgroup.card_mul_index (Kn K)]
  have hdeg : ∀ χ ∈ scriptS K,
      Work.CharCore.irrDeg χ = (Kn K).index := by
    intro χ hχ
    have h := scriptS_degree K hKcomm hcent hχ
    have h2 := Work.CharCore.irrDeg_spec
      ((mem_scriptS K).mp hχ).1
    rw [h] at h2
    exact Nat.cast_injective h2.symm
  have hfil : (Work.CharCore.Irr ↥(nrm K)).filter
        (fun θ => ((Kn K : Subgroup ↥(nrm K)) :
          Set ↥(nrm K)) ⊆ Work.CharCore.charKernel θ)
      = (Work.CharCore.Irr ↥(nrm K)).filter
          (fun θ => ¬ ∃ x : ↥(nrm K),
            (x : W) ∈ K ∧ θ x ≠ θ 1) := by
    refine Finset.filter_congr (fun θ _ => ?_)
    constructor
    · rintro h ⟨x, hx, hne⟩
      exact hne (h hx)
    · intro h x hx
      by_contra hne
      exact h ⟨x, hx, hne⟩
  have hsum_le : (∑ χ ∈ (Work.CharCore.Irr ↥(nrm K)).filter
        (fun θ => ¬ ∃ x : ↥(nrm K), (x : W) ∈ K ∧ θ x ≠ θ 1),
        ((Work.CharCore.irrDeg χ : ℝ)) ^ 2)
      = ((Kn K).index : ℝ) := by
    rw [← hfil]
    exact Work.CohApps.sum_irr_deg_sq_le_ker (Kn K)
  have hsplit : (∑ χ ∈ scriptS K, ((Work.CharCore.irrDeg χ : ℝ)) ^ 2)
      + (∑ χ ∈ (Work.CharCore.Irr ↥(nrm K)).filter
          (fun θ => ¬ ∃ x : ↥(nrm K), (x : W) ∈ K ∧ θ x ≠ θ 1),
          ((Work.CharCore.irrDeg χ : ℝ)) ^ 2)
      = (Nat.card ↥(nrm K) : ℝ) := by
    rw [← Work.CohApps.real_sum_irr_deg_sq ↥(nrm K)]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hSsq : (∑ χ ∈ scriptS K, ((Work.CharCore.irrDeg χ : ℝ)) ^ 2)
      = (Nat.card ↥(nrm K) : ℝ)
        - ((Kn K).index : ℝ) := by
    rw [hsum_le] at hsplit
    linarith
  have hepos : 0 < (Kn K).index :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := Kn K))
  have hKpos : 1 ≤ Nat.card ↥K := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨1⟩
  have hreal : ((scriptS K).card : ℝ)
      * ((Kn K).index : ℝ) = (Nat.card ↥K : ℝ) - 1 := by
    have h := hSsq
    rw [Finset.sum_congr rfl (fun χ hχ => by rw [hdeg χ hχ]), Finset.sum_const,
      nsmul_eq_mul] at h
    rw [hcardN, Nat.cast_mul] at h
    have hee : (((Kn K).index : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast hepos.ne'
    have h2 : ((scriptS K).card : ℝ)
        * ((Kn K).index : ℝ) ^ 2
        = ((Nat.card ↥K : ℝ) - 1) * ((Kn K).index : ℝ) := by
      nlinarith [h]
    have h3 : (((scriptS K).card : ℝ)
        * ((Kn K).index : ℝ) - ((Nat.card ↥K : ℝ) - 1))
        * ((Kn K).index : ℝ) = 0 := by nlinarith [h2]
    have h4 := (mul_eq_zero.mp h3).resolve_right hee
    linarith [sub_eq_zero.mp h4]
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_mul, hreal, Nat.cast_sub hKpos, Nat.cast_one]



/-- The canonical isomorphism `H.subgroupOf N ≃* H` for `H ≤ N`. -/
def subgroupOfMulEquiv {G : Type*} [Group G] {H N : Subgroup G} (h : H ≤ N) :
    ↥(H.subgroupOf N) ≃* ↥H where
  toFun := fun x => ⟨(x : G), x.2⟩
  invFun := fun y => ⟨⟨(y : G), h y.2⟩, y.2⟩
  left_inv := fun x => Subtype.ext rfl
  right_inv := fun y => Subtype.ext rfl
  map_mul' := fun a b => Subtype.ext rfl

/-- Restricting an irreducible character of `G` to a subgroup differs from restricting it
through an intermediate subgroup only by the canonical identification of the two copies of the
subgroup. -/
theorem cfInner_resFun_subgroupOf {G : Type*} [Group G] [Fintype G] {H N : Subgroup G}
    (h : H ≤ N) (f : G → ℂ) (θ : ↥H → ℂ) :
    Work.CharCore.cfInner (Work.Induction.resFun (H.subgroupOf N)
        (Work.Induction.resFun N f))
        (fun y => θ (subgroupOfMulEquiv h y))
      = Work.CharCore.cfInner (Work.Induction.resFun H f) θ := by
  have hcard : Fintype.card ↥(H.subgroupOf N) = Fintype.card ↥H :=
    Fintype.card_congr (subgroupOfMulEquiv h).toEquiv
  have hsum : (∑ y : ↥(H.subgroupOf N), f y * starRingEnd ℂ (θ (subgroupOfMulEquiv h y)))
      = ∑ k : ↥H, f k * starRingEnd ℂ (θ k) := by
    refine (Equiv.sum_comp (subgroupOfMulEquiv h).toEquiv
      (fun k : ↥H => f k * starRingEnd ℂ (θ k))).trans ?_
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rfl
  rw [Work.CharCore.cfInner_apply, Work.CharCore.cfInner_apply, hcard]
  simp only [Work.Induction.resFun_apply]
  rw [hsum]

/-- **Double counting over the union of the conjugates of `K^#`.**  For a T.I. subgroup `K ≤ W` with
`K ⊓ K^g = 1` for `g ∉ N_W(K)` and a class function `f` on `W`, the sum of `f` over the union of
the conjugates of `K^#` equals `[W : N_W(K)]` times its sum over `K^#`. -/
theorem sum_conj_into_K {W : Type*} [Group W] [Fintype W] {K : Subgroup W}
    (hTI : ∀ g : W, g ∉ Subgroup.normalizer (K : Set W) →
      K ⊓ Submission.Blueprint.conj g K = ⊥)
    (f : W → ℂ) (hf : ∀ x g : W, f (g * x * g⁻¹) = f x) :
    (∑ y : W, if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then f y else 0)
      = ((Subgroup.normalizer (K : Set W)).index : ℂ)
        * (∑ k : K, if (k : W) ≠ 1 then f (k : W) else 0) := by
  classical
  have hcardN : (Nat.card ↥(Subgroup.normalizer (K : Set W)) : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card, Nat.cast_ne_zero]
    exact Fintype.card_ne_zero
  -- ═══ writing a sum over `K` as a sum over `W` ═══
  have hKsum : ∀ (g : W → ℂ), (∑ k : K, g (k : W))
      = ∑ k : W, (if k ∈ K then g k else 0) := by
    intro g
    rw [← Finset.sum_subtype (Finset.univ.filter (fun k : W => k ∈ K)) (fun k => by simp) g,
      Finset.sum_filter]
  -- ═══ the multiplicity of each `y` in the conjugation count ═══
  have hB2 : ∀ y : W,
      (∑ x : W, (if x⁻¹ * y * x ∈ K ∧ y ≠ 1 then (1 : ℂ) else 0))
      = (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1)
          then (Nat.card ↥(Subgroup.normalizer (K : Set W)) : ℂ) else 0) := by
    intro y
    by_cases hy : ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1
    · have hy' := hy
      obtain ⟨x₀, hx₀, hy1⟩ := hy'
      have hiff : ∀ x : W,
          (x⁻¹ * y * x ∈ K) ↔ (x₀⁻¹ * x ∈ Subgroup.normalizer (K : Set W)) := by
        intro x
        constructor
        · intro hx
          by_contra hxN
          have hk1 : x₀⁻¹ * y * x₀ ≠ 1 := fun h => hy1 (by
            have hc := congrArg (fun z => x₀ * z * x₀⁻¹) h
            simpa [mul_assoc] using hc)
          have hmem : x₀⁻¹ * y * x₀ ∈ K ⊓ Submission.Blueprint.conj (x₀⁻¹ * x) K := by
            refine ⟨hx₀, ?_⟩
            change x₀⁻¹ * y * x₀ ∈ Submission.Blueprint.conj (x₀⁻¹ * x) K
            rw [mem_conj_iff]
            have he : (x₀⁻¹ * x)⁻¹ * (x₀⁻¹ * y * x₀) * (x₀⁻¹ * x) = x⁻¹ * y * x := by group
            rw [he]; exact hx
          rw [hTI _ hxN, Subgroup.mem_bot] at hmem
          exact hk1 hmem
        · intro hx
          have he : (x₀⁻¹ * x)⁻¹ * (x₀⁻¹ * y * x₀) * (x₀⁻¹ * x) = x⁻¹ * y * x := by group
          rw [← he]
          exact (Subgroup.mem_normalizer_iff''.mp hx (x₀⁻¹ * y * x₀)).mp hx₀
      have hcard : (Finset.univ.filter (fun x : W => x⁻¹ * y * x ∈ K ∧ y ≠ 1)).card
          = Nat.card ↥(Subgroup.normalizer (K : Set W)) := by
        have hset : (Finset.univ.filter (fun x : W => x⁻¹ * y * x ∈ K ∧ y ≠ 1)).card
            = (Finset.univ.filter
              (fun n : W => n ∈ Subgroup.normalizer (K : Set W))).card := by
          refine Finset.card_bij (fun x _ => x₀⁻¹ * x) ?_ ?_ ?_
          · intro x hx
            rw [Finset.mem_filter] at hx ⊢
            exact ⟨Finset.mem_univ _, (hiff x).mp hx.2.1⟩
          · intro a _ b _ h
            exact mul_left_cancel h
          · intro n hn
            rw [Finset.mem_filter] at hn
            refine ⟨x₀ * n, ?_, by group⟩
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ _, (hiff (x₀ * n)).mpr (by
              rw [show x₀⁻¹ * (x₀ * n) = n by group]; exact hn.2), hy1⟩
        rw [hset, ← Fintype.card_ofFinset (p := (Subgroup.normalizer (K : Set W) : Set W))
          (Finset.univ.filter (fun n : W => n ∈ Subgroup.normalizer (K : Set W)))
          (fun x => by simp)]
        exact Nat.card_eq_fintype_card.symm
      rw [if_pos hy, Finset.sum_boole (fun x : W => x⁻¹ * y * x ∈ K ∧ y ≠ 1) Finset.univ, hcard]
    · rw [if_neg hy]
      refine Finset.sum_eq_zero (fun x _ => ?_)
      by_cases hP : x⁻¹ * y * x ∈ K ∧ y ≠ 1
      · exact absurd ⟨x, hP⟩ hy
      · rw [if_neg hP]
  -- ═══ rewriting the inner sum by substituting `y ↦ x⁻¹ y x` ═══
  have hB1 : ∀ x : W, (∑ k : K, (if (k : W) ≠ 1 then f (x * (k : W) * x⁻¹) else 0))
      = ∑ y : W, (if x⁻¹ * y * x ∈ K ∧ y ≠ 1 then f y else 0) := by
    intro x
    rw [hKsum (fun k : W => if k ≠ 1 then f (x * k * x⁻¹) else 0)]
    rw [← Equiv.sum_comp (MulAut.conj x).toEquiv
      (fun y : W => if x⁻¹ * y * x ∈ K ∧ y ≠ 1 then f y else 0)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : k ∈ K <;> by_cases hk1 : k = 1
    · subst hk1; simp [hk]
    · have hce : (MulAut.conj x).toEquiv k = x * k * x⁻¹ := MulAut.conj_apply x k
      have e1 : x⁻¹ * (x * k * x⁻¹) * x = k := by group
      have e2 : x * k * x⁻¹ ≠ 1 := fun h => hk1 (by
        have hc := congrArg (fun z => x⁻¹ * z * x) h
        simpa [mul_assoc] using hc)
      rw [hce, e1, if_pos hk, if_pos hk1, if_pos ⟨hk, e2⟩]
    · subst hk1; simp
    · have hce : (MulAut.conj x).toEquiv k = x * k * x⁻¹ := MulAut.conj_apply x k
      have e1 : x⁻¹ * (x * k * x⁻¹) * x = k := by group
      rw [hce, e1]
      rw [if_neg hk, if_neg (fun hc => hk hc.1)]
  -- ═══ the two evaluations of the double sum ═══
  have hA : (∑ x : W, ∑ k : K, (if (k : W) ≠ 1 then f (x * (k : W) * x⁻¹) else 0))
      = (Nat.card W : ℂ) * (∑ k : K, if (k : W) ≠ 1 then f (k : W) else 0) := by
    have hpoint : ∀ x : W,
        (∑ k : K, (if (k : W) ≠ 1 then f (x * (k : W) * x⁻¹) else 0))
        = ∑ k : K, (if (k : W) ≠ 1 then f (k : W) else 0) := by
      intro x
      refine Finset.sum_congr rfl (fun k _ => ?_)
      by_cases hk : (k : W) = 1
      · simp [hk]
      · rw [if_pos hk, if_pos hk, hf (k : W) x]
    rw [Finset.sum_congr rfl (fun x _ => hpoint x), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hB : (∑ x : W, ∑ k : K, (if (k : W) ≠ 1 then f (x * (k : W) * x⁻¹) else 0))
      = (Nat.card ↥(Subgroup.normalizer (K : Set W)) : ℂ)
          * (∑ y : W, if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then f y else 0) := by
    calc (∑ x : W, ∑ k : K, (if (k : W) ≠ 1 then f (x * (k : W) * x⁻¹) else 0))
        = ∑ x : W, ∑ y : W, (if x⁻¹ * y * x ∈ K ∧ y ≠ 1 then f y else 0) :=
          Finset.sum_congr rfl (fun x _ => hB1 x)
      _ = ∑ y : W, ∑ x : W, (if x⁻¹ * y * x ∈ K ∧ y ≠ 1 then f y else 0) := Finset.sum_comm
      _ = ∑ y : W, (Nat.card ↥(Subgroup.normalizer (K : Set W)) : ℂ)
            * (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then f y else 0) := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          have hfac : ∀ x : W, (if x⁻¹ * y * x ∈ K ∧ y ≠ 1 then f y else 0)
              = f y * (if x⁻¹ * y * x ∈ K ∧ y ≠ 1 then (1 : ℂ) else 0) := by
            intro x
            by_cases hP : x⁻¹ * y * x ∈ K ∧ y ≠ 1 <;> simp [hP]
          rw [Finset.sum_congr rfl (fun x _ => hfac x), ← Finset.mul_sum, hB2 y]
          by_cases hy : ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1 <;> simp [hy, mul_comm]
      _ = (Nat.card ↥(Subgroup.normalizer (K : Set W)) : ℂ)
            * ∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then f y else 0) :=
          (Finset.mul_sum _ _ _).symm
  have h1 := hA
  rw [hB] at h1
  have h2 : (Nat.card W : ℂ) = (Nat.card ↥(Subgroup.normalizer (K : Set W)) : ℂ)
      * ((Subgroup.normalizer (K : Set W)).index : ℂ) := by
    rw [← Nat.cast_mul, Subgroup.card_mul_index]
  rw [h2, mul_assoc] at h1
  exact mul_left_cancel₀ hcardN h1

/-- The value of an irreducible character is an algebraic integer. -/
theorem isIntegral_irr_apply {G : Type*} [Group G] [Fintype G] {χ : G → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr G) (x : G) : IsIntegral ℤ (χ x) := by
  obtain ⟨V, hV, hVχ⟩ := (Work.CharCore.mem_Irr_iff_fdrep χ).mp hχ
  have h := Representation.isIntegral_character V.ρ x
  rw [show Representation.character V.ρ = V.character from rfl, hVχ] at h
  exact h

/-! ## 6. The theorem


The remaining (character-theoretic) input is Suzuki's theory of exceptional characters for the
T.I.F.N. subgroup `K` (Isaacs 7.16-7.20), used exactly as in Peterfalvi, Appendix VI: `Res_K π`
is the regular character of `K`, the permutation character splits as `π = 1 + Σ ψᵢ` with the
`ψᵢ` irreducible of multiplicity one, the `ψᵢ` are exceptional (so their differences vanish off
the union of the conjugates of `K^#`), and the variance identity `Σ i(s-i)nᵢ = 0` then forces
every element outside that union to have `π y ∈ {1, |K|}`.  The elementary identity
`Σ_{y ∉ Y} (π y - 1) = [W : N_W(K)] (|K| - 1)` (for `Y` the union of the conjugates of `K^#`,
where `π` vanishes) then yields `|ker π| = [W : N_W(K)]`; since `ker π ⊓ N_W(K) = 1` this is
`ker π ⊔ N_W(K) = ⊤`.

The precise assembly is as follows.  Write `N = N_W(K)` and `H_α = W_α` for the stabiliser of
`α : I`, so that `W = K · H_α` and `K ⊓ H_α = ⊥` (`mul_K_stabilizer`, `inf_stabilizer_bot`).

* **Delegated pieces** (`Submission/Work/NormalComplement/`): `frobenius_kernel_irr`
  (`Ind_K^L θ ∈ Irr L` for nonprincipal `θ` of an abelian normal `K ◁ L` with `C_L(k) = K`,
  degree `|L|/|K|`, vanishing off `K`, and the converse), `coherent_exceptional_data`
  (Isaacs 7.13), `permutation_character_facts` (`Res_K π = reg_K`, `⟨π,1⟩ = 1`, `π`
  multiplicity-free).
* **Isometry.** `K^#` is a TI set with normalizer `N` for `Work.BrauerSuzuki.IsTISet` (extract
  from `IsTI K` and `C_W(k) = K`), so `Work.BrauerSuzuki.TI.cfInner_indFun_eq_of_TISet` gives
  that `Ind_N^W` is an isometry on the class functions supported in `K^#`; hence
  `IsometryOn S τ` for `τ := Ind_N^W` and `S = {χ ∈ Irr N | K ⊄ ker χ}`, because `ℤ[S]°`
  consists of class functions vanishing on `N ∖ K` and at `1`.
* **Coherence.** All `χ ∈ S` have degree `e = |N : K|` and `τ (χ - χ₀)` is a virtual character of
  degree zero, so `Work.Coherence.coherent_of_norm_two_lift` gives `Coherent S τ` when `|S| ≥ 2`.
* **Exceptional characters.** `coherent_exceptional_data` gives `g : S → Irr W` and `E := g '' S`.
  For a constituent `ψ ≠ 1_W` of `π`, the set `A_ψ := {μ ∈ Irr K | ⟨Res_K ψ, μ⟩ ≠ 0}` is a union
  of the `N`-orbits `A_χ` (`χ ∈ S`, all of size `e`) on `Irr K ∖ {1}`.  If the action is not
  doubly transitive then `|S| ≥ 2` and `A_ψ` is non-empty and proper; for `λ ∈ A_ψ`,
  `λ' ∉ A_ψ` Frobenius reciprocity gives `⟨Ind_K^N λ' - Ind_K^N λ, Res_N ψ⟩ = 0 - 1 ≠ 0`, so
  `ψ ∈ E`.  (`A_ψ ≠ ∅` because `⟨Res_K ψ, reg_K⟩ = ψ(1) ≠ 0`.)
* **Vanishing off `K#`.** For `ψ = g χ`, `ψ' = g χ'` in `E`, `ψ - ψ' = ε (χ - χ')^W` since
  `χ - χ' ∈ ℤ[S]°` and `τ'` agrees with induction there; and `Ind_N^W χ` vanishes outside the
  conjugates of `K^#` because `χ` vanishes off `K`.  Hence all constituents of `π` other than
  `1_W` agree outside `Y := ⋃_w (K^w)^#`, so `π y = 1 + t ψ₁ y` there.
* **Counting.** `Σ_{y ∈ W} ψ = 0` for `ψ ≠ 1_W`, and the elementary identity
  `Σ_{y ∈ Y} f = [W : N] Σ_{k ∈ K^#} f k` for class functions `f` (double counting over
  `W × K^#`, using that `f` is constant on `W`-classes and the TI property), give the source's
  two moment identities, hence `Σ i (s - i) nᵢ = 0` with `nᵢ = #{y ∉ Y | ψ₁ y = i}`.  So
  `ψ₁ y ∈ {0, s}` for `y ∉ Y` and `#{y ∉ Y | ψ₁ y = s} = [W : N]`.  Finally `ψ₁ y = s` iff
  `π y = π 1` iff `y ∈ ker π` (as `π y = |Fix y|`), so `|ker π| = [W : N]`; with
  `ker_inf_normalizer_eq_bot` and `|ker π ⊔ N| = |ker π| · |N|` this is `ker π ⊔ N = ⊤`. -/

/-- **Peterfalvi I Appendix VI** (pp. 213–215), a generalisation of Burnside's result on
permutation groups of prime degree.  If `W` acts on a set `I` with `1 < |I|`, and `K ≤ W` acts
*regularly* on `I` (sharply transitively) with `C_W(k) = K` for every `k ∈ K#`, then either `W`
acts doubly transitively on `I`, or `W = C_W(I)·N_W(K)`.

This is the input of Ch. III §3 Prop. 2 (p.178).  Under the hypotheses `K` is a T.I.F.N. subgroup
of `W` (Isaacs, *Character Theory of Finite Groups*, Definition 7.16: `K` is a T.I. set,
`K ⊴ N_W(K)`, `C_W(k) ≤ K` for `1 ≠ k ∈ K`), the action is equivalent to the action on the cosets
of `N_W(K)`, and the proof runs through Suzuki's theory of exceptional characters for T.I.F.N.
subgroups (Isaacs 7.17–7.20: the set `𝒮 = {χ ∈ Irr(N_W(K)) | K ⊄ ker χ}` is coherent, the isometry
`Ind : ℤ[𝒮] → ℤ[Irr(W)]` of exceptional characters, the `|W : N_W(K)|` exceptional characters
constant off `K#`, and the variance identity `Σ i(s-i)nᵢ = 0`).  In the application the permutation
character is `π = 1_W + ψ₁ + … + ψ_t`, and if `t ≥ 2` and `N_W(K) ≠ K` then the `ψᵢ` are the
exceptional characters.

Available character-theory machinery in the workspace: `Submission.Work.Coherence`
(`Coherent`, `cfInner`, isometry extension), `Submission.Work.Clifford` (Clifford
correspondence, `Irr` as a `Finset`, Galois action on `Irr`), `Submission.Work.Induction`
(`indFun`, Frobenius reciprocity, `cfInner_indFun_eq_of_TI`), `Submission.Work.Frobenius.Char`
(irreducibility and orthonormality of `Irr`), and `Submission.Work.CharCore` (`irr_orthonormal`,
`classFun_eq_sum_irr`). -/
theorem appVI_fintype {W : Type*} [Group W] [Fintype W] {I : Type*} [Fintype I]
    [MulAction W I] {K : Subgroup W} (hI : 1 < Fintype.card I)
    (hreg : ∀ i j : I, ∃! k : K, (k : W) • i = j)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) = K) :
    MulAction.IsMultiplyPretransitive W I 2 ∨
      (MulAction.toPermHom W I).ker ⊔ Subgroup.normalizer (K : Set W) = ⊤ := by
  classical
  by_cases h2 : MulAction.IsMultiplyPretransitive W I 2
  · exact Or.inl h2
  right
  -- ═══ set-up ═══
  haveI : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  set α : I := Classical.arbitrary I
  have htr : MulAction.IsPretransitive W I := W_pretransitive hreg
  haveI : MulAction.IsPretransitive W I := htr
  have hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := K_commutative hcent
  have hcent' : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K :=
    fun k hk hk1 => le_of_eq (hcent k hk hk1)
  haveI : IsMulCommutative K :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (hKcomm a a.2 b b.2))
  have hTI : ∀ g : W, g ∉ Subgroup.normalizer (K : Set W) →
      K ⊓ Submission.Blueprint.conj g K = ⊥ := K_isTI hreg hcent
  have hKne : K ≠ ⊥ := K_ne_bot hI hreg
  have hKcard : Nat.card K = Fintype.card I := by
    have h1 := stabilizer_index_eq_card α hreg
    have h2 : (MulAction.stabilizer W α).index = Nat.card I :=
      MulAction.index_stabilizer_of_transitive W α
    rw [h1] at h2
    exact h2.trans Nat.card_eq_fintype_card
  have hKgt : 1 < Nat.card K := by rw [hKcard]; exact hI
  set π : W → ℂ := Work.Induction.indFun (MulAction.stabilizer W α)
      (fun _ : MulAction.stabilizer W α => (1 : ℂ))
  obtain ⟨hπk0, hπ10, hπinner0, hπmult0⟩ := permutation_character_facts α hreg hcent
  have hπk : ∀ k : K, k ≠ 1 → π (k : W) = 0 := hπk0
  have hπ1 : π 1 = (Nat.card K : ℂ) := hπ10
  have hπinner : Work.CharCore.cfInner π (1 : W → ℂ) = 1 := hπinner0
  have hπmult : ∀ χ ∈ Work.CharCore.Irr W, Work.CharCore.cfInner π χ ≠ 0 →
      Work.CharCore.cfInner π χ = 1 := hπmult0
  -- ═══ the decomposition π = 1 + Σ_{χ ∈ T} χ ═══
  set T : Finset (W → ℂ) :=
    (Work.CharCore.Irr W).filter (fun χ => χ ≠ 1 ∧ Work.CharCore.cfInner π χ ≠ 0)
  have hTmem : ∀ χ ∈ T, χ ∈ Work.CharCore.Irr W ∧ χ ≠ 1 ∧
      Work.CharCore.cfInner π χ ≠ 0 := fun χ hχ => Finset.mem_filter.mp hχ
  have hdecomp : π = 1 + ∑ χ ∈ T, χ := by
    have hclass : Work.CharCore.IsClassFun π := Work.Induction.isClassFun_indFun _ _
    have hIrr1 : (1 : W → ℂ) ∈ Work.CharCore.Irr W := Work.CharCore.principalChar_mem_Irr
    rw [Work.CharCore.classFun_eq_sum_irr hclass]
    rw [← Finset.sum_filter_add_sum_filter_not (Work.CharCore.Irr W)
      (fun χ => χ ≠ 1 ∧ Work.CharCore.cfInner π χ ≠ 0)
      (fun χ => (Work.CharCore.cfInner π χ) • χ)]
    have hT1 : (∑ χ ∈ (Work.CharCore.Irr W).filter
          (fun χ => χ ≠ 1 ∧ Work.CharCore.cfInner π χ ≠ 0),
          (Work.CharCore.cfInner π χ) • χ) = ∑ χ ∈ T, χ := by
      refine Finset.sum_congr rfl (fun χ hχ => ?_)
      rw [(hπmult χ (hTmem χ hχ).1 (hTmem χ hχ).2.2), one_smul]
    have hone : (∑ χ ∈ (Work.CharCore.Irr W).filter
          (fun χ => ¬(χ ≠ 1 ∧ Work.CharCore.cfInner π χ ≠ 0)),
          (Work.CharCore.cfInner π χ) • χ) = (1 : W → ℂ) := by
      have hsingle : (∑ χ ∈ (Work.CharCore.Irr W).filter
            (fun χ => ¬(χ ≠ 1 ∧ Work.CharCore.cfInner π χ ≠ 0)),
            (Work.CharCore.cfInner π χ) • χ)
          = (Work.CharCore.cfInner π (1 : W → ℂ)) • (1 : W → ℂ) := by
        refine Finset.sum_eq_single (1 : W → ℂ) ?_ ?_
        · intro b hb hb1
          have hb' := Finset.mem_filter.mp hb
          have hzero : Work.CharCore.cfInner π b = 0 := by
            by_contra hcon
            exact hb'.2 ⟨hb1, hcon⟩
          rw [hzero, zero_smul]
        · intro hnot
          exact absurd (Finset.mem_filter.mpr ⟨hIrr1, fun hc => hc.1 rfl⟩) hnot
      rw [hsingle, hπinner, one_smul]
    rw [hT1, hone, add_comm]
  have hTne : T.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    have h1 : π 1 = (1 : ℂ) := by
      rw [hdecomp, hcon, Finset.sum_empty]
      simp
    rw [hπ1] at h1
    have h2 : Nat.card K = 1 := Nat.cast_injective (by simpa using h1 : ((Nat.card K : ℕ) : ℂ) = ((1 : ℕ) : ℂ))
    omega
  have hTcard2 : 2 ≤ T.card := by
    by_contra hcon
    have hcard1 : T.card = 1 := by
      have := Finset.card_pos.mpr hTne
      omega
    obtain ⟨ψ, hψT⟩ := Finset.card_eq_one.mp hcard1
    have hψmem : ψ ∈ T := by rw [hψT]; exact Finset.mem_singleton_self ψ
    have hψIrr : ψ ∈ Work.CharCore.Irr W := (hTmem ψ hψmem).1
    have hdecomp' : π = 1 + ψ := by rw [hdecomp, hψT]; simp
    have hcf : Work.CharCore.cfInner π π = 2 := by
      have hc1 : Work.CharCore.cfInner (1 : W → ℂ) (1 : W → ℂ) = 1 := by
        rw [Work.CharCore.cfInner_apply]
        simp
      have hc3 : Work.CharCore.cfInner ψ (1 : W → ℂ) = 0 := by
        have h : Work.CharCore.cfInner (1 : W → ℂ) (1 : W → ℂ)
            + Work.CharCore.cfInner ψ (1 : W → ℂ) = 1 := by
          rw [← Work.CharCore.cfInner_add_left, ← hdecomp']
          exact hπinner
        rw [hc1] at h
        exact add_left_cancel (by simpa using h : (1 : ℂ) + _ = (1 : ℂ) + 0)
      have hc2 : Work.CharCore.cfInner (1 : W → ℂ) ψ = 0 := by
        rw [Work.CharCore.cfInner_conj_symm, hc3, map_zero]
      have hc4 : Work.CharCore.cfInner ψ ψ = 1 := by
        rw [Work.CharCore.irr_orthonormal ψ ψ hψIrr hψIrr, if_pos rfl]
      rw [hdecomp', Work.CharCore.cfInner_add_left, Work.CharCore.cfInner_add_right,
        Work.CharCore.cfInner_add_right, hc1, hc2, hc3, hc4]
      norm_num
    exact h2 (twoTransitive_of_cfInner_permChar_eq_two htr α hcf)
  -- ═══ the restriction of π to K ═══
  have hres : Work.Induction.resFun K π = Work.CharCore.regularChar K := by
    funext k
    rw [Work.Induction.resFun_apply]
    by_cases hk : k = 1
    · have hk1 : ((k : K) : W) = 1 := by rw [hk]; rfl
      rw [hk1, hπ1]
      simp [Work.CharCore.regularChar, hk]
    · rw [hπk k hk]
      simp [Work.CharCore.regularChar, hk]
  -- ═══ multiplicities ═══
  let mm : (W → ℂ) → (↥K → ℂ) → ℕ := fun χ μ =>
    if h : ∃ n : ℕ, Work.CharCore.cfInner (Work.Induction.resFun K χ) μ = (n : ℂ)
      then Classical.choose h else 0
  have hmm : ∀ (χ : W → ℂ) (μ : ↥K → ℂ),
      (∃ n : ℕ, Work.CharCore.cfInner (Work.Induction.resFun K χ) μ = (n : ℂ)) →
      Work.CharCore.cfInner (Work.Induction.resFun K χ) μ = (mm χ μ : ℂ) := by
    intro χ μ h
    simp only [mm]
    rw [dif_pos h]
    exact Classical.choose_spec h
  have hmmIrr : ∀ (χ : W → ℂ), χ ∈ Work.CharCore.Irr W → ∀ μ : ↥K → ℂ,
      μ ∈ Work.CharCore.Irr ↥K →
      Work.CharCore.cfInner (Work.Induction.resFun K χ) μ = (mm χ μ : ℂ) :=
    fun χ hχ μ hμ => hmm χ μ (Work.Induction.exists_nat_cfInner_resFun hχ hμ)
  -- ═══ the sum identity ═══
  have hkey : ∀ μ ∈ Work.CharCore.Irr ↥K,
      (∑ χ ∈ T, (mm χ μ : ℂ)) = if μ = (1 : ↥K → ℂ) then 0 else 1 := by
    intro μ hμ
    have hsumχ : (∑ χ ∈ T, Work.CharCore.cfInner (Work.Induction.resFun K χ) μ)
        = Work.CharCore.cfInner (Work.CharCore.regularChar K) μ
          - Work.CharCore.cfInner (Work.Induction.resFun K (1 : W → ℂ)) μ := by
      have h1 : (∑ χ ∈ T, Work.Induction.resFun K χ)
          = Work.Induction.resFun K (∑ χ ∈ T, χ) :=
        (Work.Induction.resFun_sum K T (fun χ => χ)).symm
      have h2 : Work.Induction.resFun K π
          = Work.Induction.resFun K (1 : W → ℂ) + ∑ χ ∈ T, Work.Induction.resFun K χ := by
        rw [hdecomp, Work.Induction.resFun_add, Work.Induction.resFun_sum]
      have h3 : Work.Induction.resFun K (∑ χ ∈ T, χ)
          = Work.Induction.resFun K π - Work.Induction.resFun K (1 : W → ℂ) := by
        rw [h2, ← h1]
        abel
      have h4 : Work.CharCore.cfInner (Work.Induction.resFun K π) μ
          = Work.CharCore.cfInner (Work.CharCore.regularChar K) μ := by rw [hres]
      calc (∑ χ ∈ T, Work.CharCore.cfInner (Work.Induction.resFun K χ) μ)
          = Work.CharCore.cfInner (∑ χ ∈ T, Work.Induction.resFun K χ) μ :=
            (Work.CharCore.cfInner_sum_left _ _ _).symm
        _ = Work.CharCore.cfInner (Work.Induction.resFun K (∑ χ ∈ T, χ)) μ := by rw [h1]
        _ = Work.CharCore.cfInner
              (Work.Induction.resFun K π - Work.Induction.resFun K (1 : W → ℂ)) μ := by rw [h3]
        _ = Work.CharCore.cfInner (Work.Induction.resFun K π) μ
              - Work.CharCore.cfInner (Work.Induction.resFun K (1 : W → ℂ)) μ :=
            Work.CharCore.cfInner_sub_left _ _ _
        _ = Work.CharCore.cfInner (Work.CharCore.regularChar K) μ
              - Work.CharCore.cfInner (Work.Induction.resFun K (1 : W → ℂ)) μ := by rw [h4]
    have hcongr : (∑ χ ∈ T, Work.CharCore.cfInner (Work.Induction.resFun K χ) μ)
        = ∑ χ ∈ T, (mm χ μ : ℂ) :=
      Finset.sum_congr rfl (fun χ hχ => hmmIrr χ (hTmem χ hχ).1 μ hμ)
    rw [hcongr] at hsumχ
    rw [Work.CharCore.cfInner_regularChar hμ,
      Work.CharCore.irrDeg_eq_one_of_commutative hμ] at hsumχ
    have h1 : Work.Induction.resFun K (1 : W → ℂ) = (1 : ↥K → ℂ) := rfl
    rw [h1, Work.CharCore.irr_orthonormal (1 : ↥K → ℂ) μ
      (Work.CharCore.principalChar_mem_Irr) hμ] at hsumχ
    by_cases hμ1 : μ = (1 : ↥K → ℂ)
    · rw [if_pos (show (1 : ↥K → ℂ) = μ from hμ1.symm)] at hsumχ
      rw [if_pos hμ1, hsumχ]
      ring
    · rw [if_neg (fun h : (1 : ↥K → ℂ) = μ => hμ1 h.symm)] at hsumχ
      rw [if_neg hμ1, hsumχ]
      ring
  have hkeyN : ∀ μ ∈ Work.CharCore.Irr ↥K,
      (∑ χ ∈ T, mm χ μ) = if μ = (1 : ↥K → ℂ) then 0 else 1 := by
    intro μ hμ
    have h := hkey μ hμ
    have h2 : ((∑ χ ∈ T, mm χ μ : ℕ) : ℂ)
        = ((if μ = (1 : ↥K → ℂ) then 0 else 1 : ℕ) : ℂ) := by
      rw [Nat.cast_sum, h]
      by_cases hμ1 : μ = (1 : ↥K → ℂ) <;> simp [hμ1]
    exact Nat.cast_injective h2
  have hmmOne : ∀ ψ ∈ T, mm ψ (1 : ↥K → ℂ) = 0 := by
    intro ψ hψ
    have h := hkeyN (1 : ↥K → ℂ) (Work.CharCore.principalChar_mem_Irr (G := ↥K))
    rw [if_pos rfl] at h
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp h ψ hψ
  -- ═══ the sets `A_ψ` ═══
  have hAne : ∀ ψ ∈ T, ∃ μ ∈ Work.CharCore.Irr ↥K,
      μ ≠ (1 : ↥K → ℂ) ∧ mm ψ μ ≠ 0 := by
    intro ψ hψ
    by_contra hcon
    have hcon' : ∀ μ ∈ Work.CharCore.Irr ↥K, μ ≠ (1 : ↥K → ℂ) → mm ψ μ = 0 := by
      intro μ hμ hμ1
      by_contra hne
      exact hcon ⟨μ, hμ, hμ1, hne⟩
    have h0 : mm ψ (1 : ↥K → ℂ) = 0 := by
      have h := hkeyN (1 : ↥K → ℂ) (Work.CharCore.principalChar_mem_Irr (G := ↥K))
      rw [if_pos rfl] at h
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp h ψ hψ
    have hclassψ : Work.CharCore.IsClassFun (Work.Induction.resFun K ψ) :=
      Work.Induction.isClassFun_resFun (Work.CharCore.isClassFun_of_mem_Irr (hTmem ψ hψ).1)
    have hzero : Work.Induction.resFun K ψ = 0 := by
      rw [Work.CharCore.classFun_eq_sum_irr hclassψ]
      refine Finset.sum_eq_zero (fun μ hμ => ?_)
      by_cases hμ1 : μ = (1 : ↥K → ℂ)
      · rw [hmmIrr ψ (hTmem ψ hψ).1 μ hμ, hμ1, h0]
        simp
      · rw [hmmIrr ψ (hTmem ψ hψ).1 μ hμ, hcon' μ hμ hμ1]
        simp
    have hψ1 : ψ 1 = 0 := by
      have h := congrFun hzero (1 : ↥K)
      simpa using h
    exact Work.CharCore.irrDeg_ne_zero (hTmem ψ hψ).1
      (by rw [← Work.CharCore.irrDeg_spec (hTmem ψ hψ).1]; exact hψ1)
  have hAproper : ∀ ψ ∈ T, ∃ μ ∈ Work.CharCore.Irr ↥K,
      μ ≠ (1 : ↥K → ℂ) ∧ mm ψ μ = 0 := by
    intro ψ hψ
    by_contra hcon
    have hcon' : ∀ μ ∈ Work.CharCore.Irr ↥K, μ ≠ (1 : ↥K → ℂ) → mm ψ μ ≠ 0 := by
      intro μ hμ hμ1
      by_contra hne
      exact hcon ⟨μ, hμ, hμ1, hne⟩
    obtain ⟨ψ', hψ'mem, hψ'ne⟩ := Finset.exists_mem_ne (s := T) (by omega : 1 < T.card) ψ
    obtain ⟨ν, hνmem, hν1, hνne⟩ := hAne ψ' hψ'mem
    have h1 : mm ψ ν ≠ 0 := hcon' ν hνmem hν1
    have hsum := hkeyN ν hνmem
    rw [if_neg hν1] at hsum
    have hsub : ({ψ, ψ'} : Finset (W → ℂ)) ⊆ T := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hψ
      · rw [Finset.mem_singleton.mp hz]; exact hψ'mem
    have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun z => mm z ν) hsub
      (fun z _ _ => Nat.zero_le _)
    rw [Finset.sum_pair hψ'ne.symm, hsum] at hle
    have h2 : 1 ≤ mm ψ ν := Nat.one_le_iff_ne_zero.mpr h1
    have h3 : 1 ≤ mm ψ' ν := Nat.one_le_iff_ne_zero.mpr hνne
    omega
  have hIrrKcard : (Work.CharCore.Irr ↥K).card = Nat.card ↥K := by
    have h := Work.CharCore.sum_irr_degree_sq (G := ↥K)
    have h2 : (∑ χ ∈ Work.CharCore.Irr ↥K, (1 : ℂ)) = (Nat.card ↥K : ℂ) := by
      rw [← h]
      refine Finset.sum_congr rfl (fun χ hχ => ?_)
      rw [Work.CharCore.irrDeg_spec hχ,
        Work.CharCore.irrDeg_eq_one_of_commutative (G := ↥K) hχ]
      norm_num
    rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h2
    exact Nat.cast_injective h2
  have hdegψ : ∀ ψ ∈ T, Work.CharCore.irrDeg ψ
      = ∑ μ ∈ Work.CharCore.Irr ↥K, mm ψ μ := by
    intro ψ hψ
    apply Nat.cast_injective (R := ℂ)
    rw [sum_cfInner_resFun_eq_deg (H := K) (hTmem ψ hψ).1, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun μ hμ => hmmIrr ψ (hTmem ψ hψ).1 μ hμ)
  have hdegsum : (∑ ψ ∈ T, Work.CharCore.irrDeg ψ) = Nat.card ↥K - 1 := by
    rw [Finset.sum_congr rfl hdegψ, Finset.sum_comm,
      Finset.sum_congr rfl (fun μ hμ => hkeyN μ hμ)]
    have hmem : (1 : ↥K → ℂ) ∈ Work.CharCore.Irr ↥K :=
      Work.CharCore.principalChar_mem_Irr (G := ↥K)
    rw [← Finset.sum_erase_add (Work.CharCore.Irr ↥K)
      (fun x : ↥K → ℂ => if x = (1 : ↥K → ℂ) then 0 else 1) hmem]
    have h1 : (if (1 : ↥K → ℂ) = (1 : ↥K → ℂ) then 0 else 1) = 0 := if_pos rfl
    rw [h1, add_zero]
    have h2 : (∑ x ∈ (Work.CharCore.Irr ↥K).erase (1 : ↥K → ℂ),
        (if x = (1 : ↥K → ℂ) then 0 else 1))
        = ((Work.CharCore.Irr ↥K).erase (1 : ↥K → ℂ)).card := by
      rw [Finset.sum_congr rfl (fun x hx => ?_), Finset.sum_const, smul_eq_mul, mul_one]
      rw [Finset.mem_erase] at hx
      exact if_neg hx.1
    rw [h2, Finset.card_erase_of_mem hmem, hIrrKcard]
  -- ═══ invariance of `mm` and the size of the orbits ═══
  have hNinv : ∀ (ψ : W → ℂ), ψ ∈ Work.CharCore.Irr W → ∀ (x : ↥(nrm K)) (μ : ↥K → ℂ),
      μ ∈ Work.CharCore.Irr ↥K →
      mm ψ (Work.Induction.conjFun K x μ) = mm ψ μ := by
    intro ψ hψ x μ hμ
    have hrec : ∀ (ν : ↥K → ℂ), Work.CharCore.cfInner (Work.Induction.resFun K ψ) ν
        = starRingEnd ℂ (Work.CharCore.cfInner (Work.Induction.indFun K ν) ψ) := by
      intro ν
      rw [Work.CharCore.cfInner_conj_symm (Work.Induction.resFun K ψ) ν,
        Work.Induction.frobenius_reciprocity K ν ψ (Work.CharCore.isClassFun_of_mem_Irr hψ)]
    have h1 : Work.CharCore.cfInner (Work.Induction.resFun K ψ)
        (Work.Induction.conjFun K x μ) = Work.CharCore.cfInner (Work.Induction.resFun K ψ) μ := by
      rw [hrec, hrec, Work.Induction.indFun_conjFun]
    have hex : ∃ n : ℕ, Work.CharCore.cfInner (Work.Induction.resFun K ψ)
        (Work.Induction.conjFun K x μ) = (n : ℂ) := by
      obtain ⟨n, hn⟩ := Work.Induction.exists_nat_cfInner_resFun hψ hμ
      exact ⟨n, by rw [h1, hn]⟩
    have h2 := hmm ψ (Work.Induction.conjFun K x μ) hex
    have h3 := hmmIrr ψ hψ μ hμ
    have : (mm ψ (Work.Induction.conjFun K x μ) : ℂ) = (mm ψ μ : ℂ) := by
      rw [← h2, h1, h3]
    exact Nat.cast_injective this
  -- conjugation by `x ∈ N_W(K)` as a multiplicative automorphism of `K`
  let σ : ↥(nrm K) → (↥K ≃* ↥K) := fun x =>
    { toFun := fun k => ⟨(x : W) * (k : W) * (x : W)⁻¹,
        (Subgroup.mem_normalizer_iff.mp x.2 (k : W)).mp k.2⟩
      invFun := fun k => ⟨(x : W)⁻¹ * (k : W) * (x : W),
        (Subgroup.mem_normalizer_iff.mp x.2 ((x : W)⁻¹ * (k : W) * (x : W))).mpr (by
          have hx : (x : W) * ((x : W)⁻¹ * (k : W) * (x : W)) * (x : W)⁻¹ = (k : W) := by group
          rw [hx]; exact k.2)⟩
      left_inv := fun k => Subtype.ext (by show (x : W)⁻¹ * ((x : W) * (k : W) * (x : W)⁻¹) * (x : W) = (k : W); group)
      right_inv := fun k => Subtype.ext (by show (x : W) * ((x : W)⁻¹ * (k : W) * (x : W)) * (x : W)⁻¹ = (k : W); group)
      map_mul' := fun a b => Subtype.ext (by
        show (x : W) * ((a : W) * (b : W)) * (x : W)⁻¹ = (x : W) * (a : W) * (x : W)⁻¹ * ((x : W) * (b : W) * (x : W)⁻¹)
        group) }
  have hconj_eq : ∀ (x : ↥(nrm K)) (μ : ↥K → ℂ), Work.Induction.conjFun K x μ = fun k => μ (σ x k) := by
    intro x μ
    ext k
    rw [Work.Induction.conjFun_apply]
    exact congrArg μ (Subtype.ext rfl)
  have hconj_irr : ∀ (x : ↥(nrm K)) (μ : ↥K → ℂ), μ ∈ Work.CharCore.Irr ↥K →
      Work.Induction.conjFun K x μ ∈ Work.CharCore.Irr ↥K := by
    intro x μ hμ
    rw [hconj_eq x μ]
    exact (Work.CharCore.mem_Irr_iff_coherence (G := ↥K)).mpr
      (Work.Clifford.irr_precomp_mulEquiv (σ x)
        ((Work.CharCore.mem_Irr_iff_coherence (G := ↥K)).mp hμ))
  have hcard_orb : ∀ (μ : ↥K → ℂ), μ ∈ Work.CharCore.Irr ↥K → μ ≠ (1 : ↥K → ℂ) →
      (Finset.univ.image (fun x : ↥(nrm K) => Work.Induction.conjFun K x μ)).card
        = (Kn K).index := by
    intro μ hμ hμ1
    set eK : ↥(Kn K) ≃* ↥K :=
      { toFun := fun y => ⟨(y : W), y.2⟩
        invFun := fun k => ⟨⟨(k : W), le_nrm K k.2⟩, k.2⟩
        left_inv := fun y => Subtype.ext rfl
        right_inv := fun k => Subtype.ext rfl
        map_mul' := fun a b => Subtype.ext rfl }
    set μ' : ↥(Kn K) → ℂ := fun y => μ (eK y)
    have hμ'irr : μ' ∈ Work.CharCore.Irr ↥(Kn K) :=
      (Work.CharCore.mem_Irr_iff_coherence (G := ↥(Kn K))).mpr
        (Work.Clifford.irr_precomp_mulEquiv eK
          ((Work.CharCore.mem_Irr_iff_coherence (G := ↥K)).mp hμ))
    have hμ'1 : μ' ≠ (1 : ↥(Kn K) → ℂ) := by
      intro hcon
      apply hμ1
      funext k
      obtain ⟨y, hy⟩ := eK.surjective k
      have h : μ (eK y) = 1 := by
        simpa [μ'] using congrFun hcon y
      rw [hy] at h
      exact h
    have hcomm : ∀ (x : ↥(nrm K)),
        (fun y : ↥(Kn K) => Work.Induction.conjFun K x μ (eK y))
          = Work.Clifford.conjFun (Kn K) x μ' := by
      intro x
      ext y
      rw [Work.Clifford.conjFun_apply, Work.Induction.conjFun_apply]
      exact congrArg μ (Subtype.ext rfl)
    have himg : (Finset.univ.image (fun x : ↥(nrm K) => Work.Induction.conjFun K x μ)).image
          (fun f : ↥K → ℂ => fun y : ↥(Kn K) => f (eK y))
        = Work.Clifford.charOrbit (Kn K) μ' := by
      rw [Finset.image_image]
      exact Finset.image_congr (fun x _ => hcomm x)
    have hinj : Function.Injective (fun f : ↥K → ℂ => fun y : ↥(Kn K) => f (eK y)) := by
      intro f g hfg
      funext k
      obtain ⟨y, hy⟩ := eK.surjective k
      have h := congrFun hfg y
      simpa [hy] using h
    have hcardeq : (Finset.univ.image (fun x : ↥(nrm K) => Work.Induction.conjFun K x μ)).card
        = (Work.Clifford.charOrbit (Kn K) μ').card := by
      have hh := congrArg Finset.card himg
      rw [Finset.card_image_of_injective _ hinj] at hh
      exact hh
    rw [hcardeq, Work.Clifford.card_charOrbit, inertia_eq K hcent' hμ'irr hμ'1]
  -- ═══ |S| ≥ 2 ═══
  have hSge2 : 2 ≤ (scriptS K).card := by
    have hepos : 0 < (Kn K).index :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := Kn K))
    have h1 : ∀ ψ ∈ T, (Kn K).index ≤ Work.CharCore.irrDeg ψ := by
      intro ψ hψ
      obtain ⟨μ, hμirr, hμ1, hμne⟩ := hAne ψ hψ
      have hsub : (Finset.univ.image (fun x : ↥(nrm K) => Work.Induction.conjFun K x μ))
          ⊆ (Work.CharCore.Irr ↥K).filter (fun ν => mm ψ ν ≠ 0) := by
        intro g hg
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hg
        exact Finset.mem_filter.mpr ⟨hconj_irr x μ hμirr,
          by rw [hNinv ψ (hTmem ψ hψ).1 x μ hμirr]; exact hμne⟩
      have h2 : (Finset.univ.image (fun x : ↥(nrm K) => Work.Induction.conjFun K x μ)).card
          ≤ ((Work.CharCore.Irr ↥K).filter (fun ν => mm ψ ν ≠ 0)).card :=
        Finset.card_le_card hsub
      rw [hcard_orb μ hμirr hμ1] at h2
      -- bound by the degree
      have h3 : ((Work.CharCore.Irr ↥K).filter (fun ν => mm ψ ν ≠ 0)).card
          ≤ ∑ ν ∈ Work.CharCore.Irr ↥K, mm ψ ν := by
        have hAcm : ((Work.CharCore.Irr ↥K).filter (fun ν => mm ψ ν ≠ 0)).card
            = ((Work.CharCore.Irr ↥K).filter (fun ν => mm ψ ν ≠ 0)).sum (fun _ => 1) := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
        rw [hAcm]
        refine le_trans (Finset.sum_le_sum (fun ν hν => ?_))
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun z _ _ => Nat.zero_le _))
        rw [Finset.mem_filter] at hν
        exact Nat.one_le_iff_ne_zero.mpr hν.2
      rw [hdegψ ψ hψ]
      exact le_trans h2 h3
    have h2 : T.card * (Kn K).index ≤ ∑ ψ ∈ T, Work.CharCore.irrDeg ψ := by
      have h4 : T.card * (Kn K).index = ∑ _ψ ∈ T, (Kn K).index := by
        rw [Finset.sum_const, smul_eq_mul]
      rw [h4]
      exact Finset.sum_le_sum (fun ψ hψ => h1 ψ hψ)
    rw [hdegsum, ← scriptS_card_mul_index hKcomm hcent'] at h2
    have := Nat.le_of_mul_le_mul_right h2 hepos
    omega
  -- ═══ Stage B: the exceptional characters (Isaacs 7.13) ═══
  have hS : ∀ χ ∈ scriptS K, χ ∈ Work.Coherence.Irr ↥(nrm K) := fun χ hχ =>
    (Work.CharCore.mem_Irr_iff_coherence (G := ↥(nrm K))).mp (scriptS_subset_Irr K hχ)
  have hdegd : ∃ d : ℂ, d ≠ 0 ∧ ∀ χ ∈ scriptS K, χ 1 = d :=
    ⟨((Kn K).index : ℂ),
      by exact_mod_cast (Nat.pos_of_ne_zero
        (Subgroup.index_ne_zero_of_finite (H := Kn K))).ne',
      fun χ hχ => scriptS_degree K hKcomm hcent' hχ⟩
  have hdeg0 : ∀ α ∈ Work.Coherence.ZSpan0 (scriptS K), indLinK K α 1 = 0 := by
    intro α hα
    show Work.Induction.indFun (nrm K) α 1 = 0
    rw [Work.Induction.indFun_apply_one]
    exact mul_eq_zero_of_right _ ((Work.Coherence.mem_zSpan0).mp hα).2
  have hcoh : Work.Coherence.Coherent (scriptS K) (indLinK K) :=
    exc_char_coherent K hTI hKcomm hcent'
  obtain ⟨τ', g, ε, hagree, hiso, hvchar, heps, hgε, hgirr, hginj, himg⟩ :=
    coherent_exceptional_data' (N := ↥(nrm K)) (W := W) (S := scriptS K) (tau := indLinK K)
      hSge2 hS hdegd hdeg0 hcoh
  -- ═══ Stage C: the constituents of π are exceptional ═══
  have hKcN : ∀ k ∈ Kn K, k ≠ 1 →
      Subgroup.centralizer ({k} : Set ↥(nrm K)) = Kn K := by
    intro k hk hk1
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      have hmem : ((x : ↥(nrm K)) : W) ∈ Subgroup.centralizer ({(k : W)} : Set W) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg (fun z : ↥(nrm K) => (z : W)) hx
      rw [hcent (k : W) hk (fun h => hk1 (Subtype.ext h))] at hmem
      exact Subgroup.mem_subgroupOf.mpr hmem
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (by
        show ((x : ↥(nrm K)) : W) * ((k : ↥(nrm K)) : W)
          = ((k : ↥(nrm K)) : W) * ((x : ↥(nrm K)) : W)
        exact hKcomm (x : W) (Subgroup.mem_subgroupOf.mp hx) (k : W) hk)
  have hKneN : Kn K ≠ ⊥ := by
    intro hbot
    have hforall : ∀ x : ↥(nrm K), x ∈ Kn K → x = 1 :=
      (Subgroup.eq_bot_iff_forall (H := Kn K)).mp hbot
    have h1 : ∀ x : ↥(Kn K), x = 1 := fun x => Subtype.ext (hforall ↑x x.2)
    have h2 : ∀ k : ↥K, k = 1 := by
      intro k
      have h := congrArg (subgroupOfMulEquiv (le_nrm K)) (h1 ((subgroupOfMulEquiv (le_nrm K)).symm k))
      simpa using h
    have hle : Fintype.card ↥K ≤ 1 := by
      haveI : Subsingleton ↥K := ⟨fun a b => (h2 a).trans (h2 b).symm⟩
      exact Fintype.card_le_one_iff_subsingleton.mpr ‹Subsingleton ↥K›
    have hge : 1 ≤ Fintype.card ↥K := Fintype.card_pos_iff.mpr ⟨1⟩
    have : Nat.card ↥K = 1 := by rw [Nat.card_eq_fintype_card]; omega
    omega
  have hfrob := frobenius_kernel_irr (L := ↥(nrm K)) (K := Kn K)
    (kn_normal K) hKneN hKcN (fun a ha b hb => Subtype.ext
      (hKcomm (a : W) (Subgroup.mem_subgroupOf.mp ha) (b : W) (Subgroup.mem_subgroupOf.mp hb)))
  have hψinE : ∀ ψ ∈ T, ∃ χ ∈ scriptS K, g χ = ψ := by
    intro ψ hψ
    obtain ⟨μ₀, hμ₀irr, hμ₀ne1, hμ₀nz⟩ := hAne ψ hψ
    obtain ⟨μ₁, hμ₁irr, hμ₁ne1, hμ₁z⟩ := hAproper ψ hψ
    set θ₀ : ↥(Kn K) → ℂ := fun y => μ₀ (subgroupOfMulEquiv (le_nrm K) y)
    set θ₁ : ↥(Kn K) → ℂ := fun y => μ₁ (subgroupOfMulEquiv (le_nrm K) y)
    have hθ₀irr : θ₀ ∈ Work.CharCore.Irr ↥(Kn K) :=
      (Work.CharCore.mem_Irr_iff_coherence (G := ↥(Kn K))).mpr
        (Work.Clifford.irr_precomp_mulEquiv (subgroupOfMulEquiv (le_nrm K))
          ((Work.CharCore.mem_Irr_iff_coherence (G := ↥K)).mp hμ₀irr))
    have hθ₁irr : θ₁ ∈ Work.CharCore.Irr ↥(Kn K) :=
      (Work.CharCore.mem_Irr_iff_coherence (G := ↥(Kn K))).mpr
        (Work.Clifford.irr_precomp_mulEquiv (subgroupOfMulEquiv (le_nrm K))
          ((Work.CharCore.mem_Irr_iff_coherence (G := ↥K)).mp hμ₁irr))
    have hθ₀1 : θ₀ ≠ 1 := by
      intro hcon
      apply hμ₀ne1
      funext k
      obtain ⟨y, hy⟩ := (subgroupOfMulEquiv (le_nrm K)).surjective k
      have h := congrFun hcon y
      simpa [θ₀, hy] using h
    have hθ₁1 : θ₁ ≠ 1 := by
      intro hcon
      apply hμ₁ne1
      funext k
      obtain ⟨y, hy⟩ := (subgroupOfMulEquiv (le_nrm K)).surjective k
      have h := congrFun hcon y
      simpa [θ₁, hy] using h
    have hlam : Work.Induction.indFun (Kn K) θ₀ ∈ scriptS K := by
      rw [mem_scriptS K]
      exact ⟨(hfrob.1 θ₀ hθ₀irr hθ₀1).1, (hfrob.1 θ₀ hθ₀irr hθ₀1).2.1⟩
    have hlam' : Work.Induction.indFun (Kn K) θ₁ ∈ scriptS K := by
      rw [mem_scriptS K]
      exact ⟨(hfrob.1 θ₁ hθ₁irr hθ₁1).1, (hfrob.1 θ₁ hθ₁irr hθ₁1).2.1⟩
    have hΘmem : Work.Induction.indFun (Kn K) θ₀ - Work.Induction.indFun (Kn K) θ₁
        ∈ Work.Coherence.ZSpan0 (scriptS K) := by
      refine ⟨AddSubgroup.sub_mem _ (Work.Coherence.self_mem_zSpan hlam)
        (Work.Coherence.self_mem_zSpan hlam'), ?_⟩
      show (Work.Induction.indFun (Kn K) θ₀ - Work.Induction.indFun (Kn K) θ₁) 1 = 0
      rw [Pi.sub_apply]
      have h1 : Work.Induction.indFun (Kn K) θ₀ 1 = Work.Induction.indFun (Kn K) θ₁ 1 := by
        rw [Work.Induction.indFun_eq_charCore, Work.Induction.indFun_eq_charCore,
          (hfrob.1 θ₀ hθ₀irr hθ₀1).2.2.1, (hfrob.1 θ₁ hθ₁irr hθ₁1).2.2.1]
      rw [h1, sub_self]
    have hψcl : Work.CharCore.IsClassFun ψ :=
      Work.CharCore.isClassFun_of_mem_Irr (hTmem ψ hψ).1
    have hrescl : Work.CharCore.IsClassFun
        (Work.Induction.resFun (nrm K) ψ) := Work.Induction.isClassFun_resFun hψcl
    have hcmp : ∀ (μ : ↥K → ℂ), μ ∈ Work.CharCore.Irr ↥K →
        Work.CharCore.cfInner (fun y => μ (subgroupOfMulEquiv (le_nrm K) y))
            (Work.Induction.resFun (Kn K) (Work.Induction.resFun (nrm K) ψ))
          = (mm ψ μ : ℂ) := by
      intro μ hμ
      rw [Work.CharCore.cfInner_conj_symm, cfInner_resFun_subgroupOf (le_nrm K) ψ μ,
        hmmIrr ψ (hTmem ψ hψ).1 μ hμ]
      simp
    have hstep : ∀ (θ : ↥(Kn K) → ℂ),
        Work.CharCore.cfInner ((indLinK K) (Work.Induction.indFun (Kn K) θ)) ψ
          = Work.CharCore.cfInner θ
              (Work.Induction.resFun (Kn K) (Work.Induction.resFun (nrm K) ψ)) := by
      intro θ
      rw [show (indLinK K) (Work.Induction.indFun (Kn K) θ)
          = Work.Induction.indFun (nrm K) (Work.Induction.indFun (Kn K) θ) from rfl,
        Work.Induction.frobenius_reciprocity (nrm K) _ ψ hψcl,
        Work.Induction.frobenius_reciprocity (Kn K) θ (Work.Induction.resFun (nrm K) ψ) hrescl]
    have hval : Work.CharCore.cfInner
        (τ' (Work.Induction.indFun (Kn K) θ₀ - Work.Induction.indFun (Kn K) θ₁)) ψ ≠ 0 := by
      rw [hagree _ hΘmem, map_sub, Work.CharCore.cfInner_sub_left, hstep θ₀, hstep θ₁,
        hcmp μ₀ hμ₀irr, hcmp μ₁ hμ₁irr, hμ₁z]
      simp only [Nat.cast_zero, sub_zero]
      exact_mod_cast hμ₀nz
    exact (himg ψ ((Work.CharCore.mem_Irr_iff_coherence (G := W)).mp (hTmem ψ hψ).1)).mpr
      ⟨_, hΘmem, hval⟩
  -- ═══ Stage D: vanishing off the conjugates of `K^#`, and the moments ═══
  obtain ⟨ψ₁, hψ₁T⟩ := hTne
  obtain ⟨ψ₂, hψ₂T, hψ₂ne⟩ := Finset.exists_mem_ne (s := T) (by omega : 1 < T.card) ψ₁
  have hψ₁Irr : ψ₁ ∈ Work.CharCore.Irr W := (hTmem ψ₁ hψ₁T).1
  have hψ₂Irr : ψ₂ ∈ Work.CharCore.Irr W := (hTmem ψ₂ hψ₂T).1
  have hψ₁ne1 : ψ₁ ≠ 1 := (hTmem ψ₁ hψ₁T).2.1
  have hvanish : ∀ (χ : ↥(nrm K) → ℂ), χ ∈ scriptS K → ∀ x : W,
      (∀ y : W, y * x * y⁻¹ ∉ K) → Work.Induction.indFun (nrm K) χ x = 0 := by
    intro χ hχ x hx
    rw [Work.Induction.indFun_apply_def]
    rw [Finset.sum_eq_zero (fun y _ => ?_), mul_zero]
    by_cases hy : y * x * y⁻¹ ∈ Subgroup.normalizer (K : Set W)
    · rw [dite_eq_left hy]
      by_cases hyK : y * x * y⁻¹ ∈ K
      · exact absurd hyK (hx y)
      · exact scriptS_vanish K hcent' hχ (x := ⟨y * x * y⁻¹, hy⟩) hyK
    · rw [dite_eq_right hy]
  have hsub0 : ∀ χ χ' : ↥(nrm K) → ℂ, χ ∈ scriptS K → χ' ∈ scriptS K →
      χ - χ' ∈ Work.Coherence.ZSpan0 (scriptS K) := by
    intro χ χ' hχ hχ'
    refine ⟨AddSubgroup.sub_mem _ (Work.Coherence.self_mem_zSpan hχ)
      (Work.Coherence.self_mem_zSpan hχ'), ?_⟩
    show (χ - χ') 1 = 0
    rw [Pi.sub_apply, scriptS_degree K hKcomm hcent' hχ, scriptS_degree K hKcomm hcent' hχ',
      sub_self]
  have hτdeg : ∀ χ ∈ scriptS K, ∀ χ' ∈ scriptS K, (τ' χ) 1 = (τ' χ') 1 := by
    intro χ hχ χ' hχ'
    have hZm := hsub0 χ χ' hχ hχ'
    have h1 : τ' (χ - χ') = indLinK K (χ - χ') := hagree _ hZm
    have h2 := congrFun h1 1
    rw [map_sub, map_sub, Pi.sub_apply, Pi.sub_apply] at h2
    have h3 : ∀ θ ∈ scriptS K, (indLinK K θ) 1
        = ((nrm K).index : ℂ) * ((Kn K).index : ℂ) := by
      intro θ hθ
      show Work.Induction.indFun (nrm K) θ 1 = _
      rw [Work.Induction.indFun_apply_one, scriptS_degree K hKcomm hcent' hθ]
    rw [h3 χ hχ, h3 χ' hχ', sub_self] at h2
    exact sub_eq_zero.mp h2
  have hdegs : ∀ ψ ∈ T, ∀ ψ' ∈ T, ψ 1 = ψ' 1 := by
    intro ψ hψ ψ' hψ'
    obtain ⟨χ, hχS, hχψ⟩ := hψinE ψ hψ
    obtain ⟨χ', hχ'S, hχ'ψ⟩ := hψinE ψ' hψ'
    rw [← hχψ, ← hχ'ψ, hgε χ hχS, hgε χ' hχ'S, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, hτdeg χ hχS χ' hχ'S]
  set s : ℂ := (Work.CharCore.irrDeg ψ₁ : ℂ)
  have hs : ∀ ψ ∈ T, ψ 1 = s := fun ψ hψ =>
    (hdegs ψ hψ ψ₁ hψ₁T).trans (Work.CharCore.irrDeg_spec hψ₁Irr)
  have hs1 : s = ψ₁ 1 := (hs ψ₁ hψ₁T).symm
  have hsne : s ≠ 0 := by
    rw [hs1, Work.CharCore.irrDeg_spec hψ₁Irr]
    exact Work.CharCore.irrDeg_ne_zero hψ₁Irr
  have hstar_s : starRingEnd ℂ s = s := by
    rw [hs1, Work.CharCore.irrDeg_spec hψ₁Irr, map_natCast]
  -- the value of `ψ` off `Y`
  have hofY : ∀ ψ ∈ T, ∀ y : W, (∀ x : W, x * y * x⁻¹ ∉ K) → ψ y = ψ₁ y := by
    intro ψ hψ y hy
    obtain ⟨χ, hχS, hχψ⟩ := hψinE ψ hψ
    obtain ⟨χ₁, hχ₁S, hχ₁ψ⟩ := hψinE ψ₁ hψ₁T
    rw [← hχψ, ← hχ₁ψ]
    have hZm := hsub0 χ χ₁ hχS hχ₁S
    have h1 : g χ - g χ₁ = ε • (Work.Induction.indFun (nrm K) χ
        - Work.Induction.indFun (nrm K) χ₁) := by
      rw [hgε χ hχS, hgε χ₁ hχ₁S, ← smul_sub]
      congr 1
      rw [← LinearMap.map_sub, hagree _ hZm, map_sub]
      rfl
    have h2 : Work.Induction.indFun (nrm K) χ y - Work.Induction.indFun (nrm K) χ₁ y = 0 := by
      rw [hvanish χ hχS y hy, hvanish χ₁ hχ₁S y hy, sub_zero]
    have h3 := congrFun h1 y
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h3
    rw [h2, mul_zero] at h3
    exact sub_eq_zero.mp h3
  -- the moments
  have hIsC : ∀ ψ ∈ T, ∀ x z : W, ψ (z * x * z⁻¹) = ψ x := fun ψ hψ x z =>
    Work.CharCore.isClassFun_of_mem_Irr (hTmem ψ hψ).1 x z
  have hsumW : (∑ y : W, ψ₁ y) = 0 := by
    have h1 : Work.CharCore.cfInner ψ₁ (1 : W → ℂ) = 0 := by
      rw [Work.CharCore.irr_orthonormal ψ₁ 1 hψ₁Irr
        (Work.CharCore.principalChar_mem_Irr), if_neg hψ₁ne1]
    rw [Work.CharCore.cfInner_apply] at h1
    simp only [Pi.one_apply, map_one, mul_one] at h1
    have hne : ((Fintype.card W : ℕ) : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero
    exact (mul_eq_zero.mp h1).resolve_left (inv_ne_zero hne)
  have hsumK1 : (∑ k : K, ψ₁ (k : W)) = 0 := by
    have h1 : Work.CharCore.cfInner (Work.Induction.resFun K ψ₁) (1 : ↥K → ℂ) = 0 := by
      rw [hmmIrr ψ₁ hψ₁Irr (1 : ↥K → ℂ) (Work.CharCore.principalChar_mem_Irr (G := ↥K)),
        hmmOne ψ₁ hψ₁T]
      norm_num
    have h2 : (∑ k : K, ψ₁ (k : W)) = (Nat.card ↥K : ℂ)
        * Work.CharCore.cfInner (Work.Induction.resFun K ψ₁) (1 : ↥K → ℂ) := by
      rw [Work.CharCore.cfInner_apply]
      have hne : ((Fintype.card ↥K : ℕ) : ℂ) ≠ 0 := by
        rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero
      have hsumid : (∑ x : ↥K, (Work.Induction.resFun K ψ₁) x
            * starRingEnd ℂ ((1 : ↥K → ℂ) x)) = ∑ x : ↥K, ψ₁ (x : W) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Work.Induction.resFun_apply, Pi.one_apply, map_one, mul_one]
      rw [hsumid, Nat.card_eq_fintype_card, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [h2, h1, mul_zero]
  have hsumK1' : (∑ k : K, if (k : W) ≠ 1 then ψ₁ (k : W) else 0) = -s := by
    have h1 : (∑ k : K, ψ₁ (k : W))
        = ψ₁ (1 : W) + ∑ k : K, (if (k : W) ≠ 1 then ψ₁ (k : W) else 0) := by
      rw [← Finset.sum_erase_add (Finset.univ : Finset ↥K) (fun k : ↥K => ψ₁ (k : W))
        (Finset.mem_univ (1 : ↥K))]
      have hsum : (∑ k ∈ (Finset.univ : Finset ↥K).erase (1 : ↥K), ψ₁ (k : W))
          = ∑ k : K, (if (k : W) ≠ 1 then ψ₁ (k : W) else 0) := by
        rw [← Finset.filter_ne' (Finset.univ : Finset ↥K) (1 : ↥K), Finset.sum_filter]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        by_cases hk : k = (1 : ↥K)
        · subst hk; simp
        · have hk' : (k : W) ≠ 1 := fun h => hk (Subtype.ext h)
          rw [if_pos hk, if_pos hk']
      rw [hsum, add_comm, Subgroup.coe_one]
    rw [hsumK1, hs ψ₁ hψ₁T] at h1
    exact eq_neg_of_add_eq_zero_right h1.symm
  have hres0 : Work.CharCore.cfInner (Work.Induction.resFun K ψ₁)
      (Work.Induction.resFun K ψ₂) = 0 := by
    have hexp : Work.Induction.resFun K ψ₂ = ∑ μ ∈ Work.CharCore.Irr ↥K,
        (mm ψ₂ μ : ℂ) • (μ : ↥K → ℂ) := by
      rw [Work.CharCore.classFun_eq_sum_irr
        (Work.Induction.isClassFun_resFun (Work.CharCore.isClassFun_of_mem_Irr hψ₂Irr))]
      refine Finset.sum_congr rfl (fun μ hμ => ?_)
      rw [hmmIrr ψ₂ hψ₂Irr μ hμ]
    have hdis : ∀ μ ∈ Work.CharCore.Irr ↥K, mm ψ₁ μ * mm ψ₂ μ = 0 := by
      intro μ hμ
      have hkey := hkeyN μ hμ
      by_cases hμ1 : μ = (1 : ↥K → ℂ)
      · rw [hμ1] at hkey ⊢
        rw [if_pos rfl] at hkey
        have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hkey ψ₁ hψ₁T
        rw [h0, zero_mul]
      · rw [if_neg hμ1] at hkey
        by_cases h1 : mm ψ₁ μ = 0
        · rw [h1, zero_mul]
        · have h2 : mm ψ₂ μ = 0 := by
            by_contra h2'
            have hsub : ({ψ₁, ψ₂} : Finset (W → ℂ)) ⊆ T := by
              intro z hz
              rcases Finset.mem_insert.mp hz with rfl | hz
              · exact hψ₁T
              · rw [Finset.mem_singleton.mp hz]; exact hψ₂T
            have hle := Finset.sum_le_sum_of_subset_of_nonneg
              (f := fun χ => mm χ μ) hsub (fun z _ _ => Nat.zero_le _)
            rw [Finset.sum_pair hψ₂ne.symm] at hle
            have h3 := Nat.one_le_iff_ne_zero.mpr h1
            have h4 := Nat.one_le_iff_ne_zero.mpr h2'
            omega
          rw [h2, mul_zero]
    have hsub : Work.CharCore.cfInner (Work.Induction.resFun K ψ₂)
        (Work.Induction.resFun K ψ₁) = 0 := by
      rw [hexp, Work.CharCore.cfInner_sum_smul_left]
      refine Finset.sum_eq_zero (fun μ hμ => ?_)
      rw [Work.CharCore.cfInner_conj_symm, hmmIrr ψ₁ hψ₁Irr μ hμ, map_natCast (starRingEnd ℂ) (mm ψ₁ μ),
        ← Nat.cast_mul, Nat.mul_comm (mm ψ₂ μ) (mm ψ₁ μ), hdis μ hμ, Nat.cast_zero]
    rw [Work.CharCore.cfInner_conj_symm, hsub, map_zero]
  have hsumK2 : (∑ k : K, if (k : W) ≠ 1 then ψ₁ (k : W) * star (ψ₂ (k : W)) else 0)
      = -(s ^ 2) := by
    have h1 : (∑ k : K, ψ₁ (k : W) * star (ψ₂ (k : W)))
        = ψ₁ (1 : W) * star (ψ₂ (1 : W))
          + ∑ k : K, (if (k : W) ≠ 1 then ψ₁ (k : W) * star (ψ₂ (k : W)) else 0) := by
      rw [← Finset.sum_erase_add (Finset.univ : Finset ↥K)
        (fun k : ↥K => ψ₁ (k : W) * star (ψ₂ (k : W))) (Finset.mem_univ (1 : ↥K))]
      have hsum : (∑ k ∈ (Finset.univ : Finset ↥K).erase (1 : ↥K),
            ψ₁ (k : W) * star (ψ₂ (k : W)))
          = ∑ k : K, (if (k : W) ≠ 1 then ψ₁ (k : W) * star (ψ₂ (k : W)) else 0) := by
        rw [← Finset.filter_ne' (Finset.univ : Finset ↥K) (1 : ↥K), Finset.sum_filter]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        by_cases hk : k = (1 : ↥K)
        · subst hk; simp
        · have hk' : (k : W) ≠ 1 := fun h => hk (Subtype.ext h)
          rw [if_pos hk, if_pos hk']
      rw [hsum, add_comm, Subgroup.coe_one]
    have h2 : (∑ k : K, ψ₁ (k : W) * star (ψ₂ (k : W))) = 0 := by
      have h3 : (∑ k : K, ψ₁ (k : W) * star (ψ₂ (k : W)))
          = (Nat.card ↥K : ℂ) * Work.CharCore.cfInner (Work.Induction.resFun K ψ₁)
              (Work.Induction.resFun K ψ₂) := by
        rw [Work.CharCore.cfInner_apply]
        have hne : ((Fintype.card ↥K : ℕ) : ℂ) ≠ 0 := by
          rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero
        have hsumid : (∑ x : ↥K, (Work.Induction.resFun K ψ₁) x
              * starRingEnd ℂ ((Work.Induction.resFun K ψ₂) x))
            = ∑ x : ↥K, ψ₁ (x : W) * star (ψ₂ (x : W)) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          simp only [Work.Induction.resFun_apply]
          rfl
        rw [hsumid, Nat.card_eq_fintype_card, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
      rw [h3, hres0, mul_zero]
    rw [h2, hs ψ₁ hψ₁T, hs ψ₂ hψ₂T] at h1
    have hss : s * star s = s ^ 2 := by rw [Complex.star_def, hstar_s]; ring
    rw [hss] at h1
    exact eq_neg_of_add_eq_zero_right h1.symm
  -- ═══ the two moment identities ═══
  have hY1 : (∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then ψ₁ y else 0))
      = ((Subgroup.normalizer (K : Set W)).index : ℂ)
        * (∑ k : K, if (k : W) ≠ 1 then ψ₁ (k : W) else 0) :=
    sum_conj_into_K hTI ψ₁ (hIsC ψ₁ hψ₁T)
  have hoff1 : (∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then 0 else ψ₁ y))
      = ((Subgroup.normalizer (K : Set W)).index : ℂ) * s := by
    have hsplit : (∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then ψ₁ y else 0))
        + (∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then 0 else ψ₁ y))
        = ∑ y : W, ψ₁ y := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases h : ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1 <;> simp [h]
    rw [hsumW, hY1, hsumK1'] at hsplit
    have : ((Subgroup.normalizer (K : Set W)).index : ℂ) * (-s)
        + (∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then 0 else ψ₁ y)) = 0 := hsplit
    linear_combination this
  have hY2 : (∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then ψ₁ y * star (ψ₂ y) else 0))
      = ((Subgroup.normalizer (K : Set W)).index : ℂ)
        * (∑ k : K, if (k : W) ≠ 1 then ψ₁ (k : W) * star (ψ₂ (k : W)) else 0) :=
    sum_conj_into_K hTI (fun y => ψ₁ y * star (ψ₂ y)) (fun x z => by
      rw [hIsC ψ₁ hψ₁T x z, hIsC ψ₂ hψ₂T x z])
  have hoff2 : (∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then 0
      else ψ₁ y * star (ψ₂ y))) = ((Subgroup.normalizer (K : Set W)).index : ℂ) * s ^ 2 := by
    have hsplit : (∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1)
            then ψ₁ y * star (ψ₂ y) else 0))
        + (∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then 0
            else ψ₁ y * star (ψ₂ y))) = ∑ y : W, ψ₁ y * star (ψ₂ y) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases h : ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1 <;> simp [h]
    have hzero : (∑ y : W, ψ₁ y * star (ψ₂ y)) = 0 := by
      have h1 : Work.CharCore.cfInner ψ₁ ψ₂ = 0 := by
        rw [Work.CharCore.irr_orthonormal ψ₁ ψ₂ hψ₁Irr hψ₂Irr, if_neg (Ne.symm hψ₂ne)]
      rw [Work.CharCore.cfInner_apply] at h1
      have hne : ((Fintype.card W : ℕ) : ℂ) ≠ 0 := by
        rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero
      exact (mul_eq_zero.mp h1).resolve_left (inv_ne_zero hne)
    rw [hzero, hY2, hsumK2] at hsplit
    have : ((Subgroup.normalizer (K : Set W)).index : ℂ) * (-(s ^ 2))
        + (∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then 0
            else ψ₁ y * star (ψ₂ y))) = 0 := hsplit
    linear_combination this
  -- ═══════════════════════════════════════════════════════════════════════════════
  -- ═══════════════════════════════════════════════════════════════════════════════
  -- ═══ Stage E: the counting argument ═══
  -- ═══════════════════════════════════════════════════════════════════════════════
  have zinj : ∀ {a b : ℤ}, ((a : ℤ) : ℂ) = ((b : ℤ) : ℂ) → a = b := fun {a b} h => by
    exact_mod_cast h
  have hnotY1 : ¬ (∃ x : W, x⁻¹ * (1 : W) * x ∈ K ∧ (1 : W) ≠ 1) :=
    fun ⟨x, _, h⟩ => h rfl
  have hIK : Nat.card I = Nat.card K := by rw [hKcard, Nat.card_eq_fintype_card]
  have hsN_cast : s = ((Work.CharCore.irrDeg ψ₁ : ℤ) : ℂ) := by
    rw [hs1, Work.CharCore.irrDeg_spec hψ₁Irr]
    simp
  have hsNnz : (Work.CharCore.irrDeg ψ₁ : ℤ) ≠ 0 := by
    exact_mod_cast Work.CharCore.irrDeg_ne_zero hψ₁Irr
  have hTcard : (T.card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; omega
  have hT2z : (2 : ℤ) ≤ (T.card : ℤ) := by exact_mod_cast hTcard2
  have hTposz : (0 : ℤ) < (T.card : ℤ) := by linarith
  have hπcl : Work.CharCore.IsClassFun π := Work.Induction.isClassFun_indFun _ _
  -- `π` vanishes on `Y`
  have hπY : ∀ y : W, (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) → π y = 0 := by
    rintro y ⟨x, hx, hy1⟩
    have hk : (⟨x⁻¹ * y * x, hx⟩ : K) ≠ 1 := by
      intro h
      apply hy1
      have h2 : x⁻¹ * y * x = (1 : W) := congrArg (fun k : K => (k : W)) h
      have h3 : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
      rw [h2] at h3
      simpa using h3
    have hcl : π (x⁻¹ * y * x) = π y := by
      have h := hπcl y x⁻¹
      simpa using h
    rw [← hcl]
    exact hπk ⟨x⁻¹ * y * x, hx⟩ hk
  -- (E1) all constituents of `π` other than `1` agree with `ψ₁` off `Y`
  have hofY' : ∀ ψ ∈ T, ∀ y : W,
      (¬ ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) → ψ y = ψ₁ y := by
    intro ψ hψ y hy
    by_cases hy1 : y = 1
    · subst hy1; rw [hs ψ hψ, hs ψ₁ hψ₁T]
    · refine hofY ψ hψ y (fun x hx => hy ⟨x⁻¹, ?_, hy1⟩)
      simpa using hx
  -- (E2) `π y = 1 + t ψ₁ y` off `Y`
  have hπoff : ∀ y : W, (¬ ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) →
      π y = 1 + (T.card : ℂ) * ψ₁ y := by
    intro y hy
    have hsum : (∑ χ ∈ T, χ y) = (T.card : ℂ) * ψ₁ y := by
      rw [Finset.sum_congr rfl (fun χ hχ => hofY' χ hχ y hy), Finset.sum_const, nsmul_eq_mul]
    rw [hdecomp]
    simp only [Pi.add_apply, Pi.one_apply, Finset.sum_apply]
    rw [hsum]
  -- (E3) `π y` is the number of fixed points of `y`
  have hfix : ∀ y : W, π y = ((Nat.card (MulAction.fixedBy I y) : ℕ) : ℂ) :=
    fun y => indFun_triv_apply_eq_fixedBy htr α y
  -- (E4) `ψ₁ y` is an integer off `Y` (algebraic integer + rational)
  have hint : ∀ y : W, (¬ ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) →
      ∃ m : ℤ, ψ₁ y = (m : ℂ) := by
    intro y hy
    have hlin : (T.card : ℂ) * ψ₁ y
        = ((Nat.card (MulAction.fixedBy I y) : ℕ) : ℂ) - 1 := by
      have h1 := hπoff y hy
      have h2 := hfix y
      linear_combination h2 - h1
    have hdiv : ψ₁ y
        = (((Nat.card (MulAction.fixedBy I y) : ℕ) : ℂ) - 1) / (T.card : ℂ) := by
      rw [eq_div_iff hTcard, mul_comm]
      exact hlin
    set q : ℚ := ((Nat.card (MulAction.fixedBy I y) : ℚ) - 1) / (T.card : ℚ) with hqdef
    have hq : (q : ℂ) = ψ₁ y := by
      rw [hqdef]
      push_cast
      exact hdiv.symm
    have hIq : IsIntegral ℤ (q : ℂ) := by rw [hq]; exact isIntegral_irr_apply hψ₁Irr y
    obtain ⟨m, hm⟩ := rat_eq_int_of_isIntegral hIq
    exact ⟨m, by rw [← hq, hm, Rat.cast_intCast]⟩
  -- (E5) the integer values `mf` and their bounds
  let mf : W → ℤ := fun y => if h : ∃ m : ℤ, ψ₁ y = (m : ℂ) then Classical.choose h else 0
  have hmf : ∀ y : W, (∃ m : ℤ, ψ₁ y = (m : ℂ)) → ψ₁ y = ((mf y : ℤ) : ℂ) := by
    intro y h
    simp only [mf]
    rw [dif_pos h]
    exact Classical.choose_spec h
  have hbound : ∀ y : W, (¬ ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) →
      0 ≤ mf y ∧ mf y ≤ (Work.CharCore.irrDeg ψ₁ : ℤ) := by
    intro y hy
    have hmfy : ψ₁ y = ((mf y : ℤ) : ℂ) := hmf y (hint y hy)
    have hlin : ((Nat.card (MulAction.fixedBy I y) : ℕ) : ℤ) = 1 + (T.card : ℤ) * mf y := by
      apply zinj
      push_cast
      rw [← hfix y, hπoff y hy, hmfy]
    have hI1 : ((Nat.card I : ℕ) : ℤ)
        = 1 + (T.card : ℤ) * (Work.CharCore.irrDeg ψ₁ : ℤ) := by
      apply zinj
      push_cast
      rw [show ((Nat.card I : ℕ) : ℂ) = ((Nat.card K : ℕ) : ℂ) from by rw [hIK],
        ← hπ1, hπoff 1 hnotY1, hs ψ₁ hψ₁T]
    have hnle : ((Nat.card (MulAction.fixedBy I y) : ℕ) : ℤ) ≤ (Nat.card I : ℤ) := by
      have h := Nat.card_le_card_of_injective (f := fun i : MulAction.fixedBy I y => (i : I))
        (fun a b hab => Subtype.ext hab)
      exact_mod_cast h
    constructor
    · by_contra hcon
      have h1 : mf y ≤ -1 := by omega
      have h2 : (T.card : ℤ) * mf y ≤ -2 := by nlinarith
      have hn0 : (0 : ℤ) ≤ ((Nat.card (MulAction.fixedBy I y) : ℕ) : ℤ) := Int.natCast_nonneg _
      linarith
    · have hmul : (T.card : ℤ) * mf y
          ≤ (T.card : ℤ) * (Work.CharCore.irrDeg ψ₁ : ℤ) := by linarith
      exact le_of_mul_le_mul_left hmul hTposz
  -- (E6) the variance identity
  have hstarY : ∀ y : W, (¬ ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) →
      ψ₁ y * ψ₁ y = ψ₁ y * star (ψ₂ y) := by
    intro y hy
    have h1 : ψ₂ y = ψ₁ y := hofY' ψ₂ hψ₂T y hy
    rw [h1, hmf y (hint y hy), star_intCast]
  have hvarC : (∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then (0 : ℂ)
      else ψ₁ y * (s - ψ₁ y))) = 0 := by
    have h2' : (∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then (0 : ℂ)
        else ψ₁ y * ψ₁ y)) = ((Subgroup.normalizer (K : Set W)).index : ℂ) * s ^ 2 := by
      rw [← hoff2]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases h : ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
        exact hstarY y h
    have hsplit : (∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then (0 : ℂ)
        else ψ₁ y * (s - ψ₁ y)))
        = s * (∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then (0 : ℂ)
            else ψ₁ y))
          - (∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then (0 : ℂ)
            else ψ₁ y * ψ₁ y)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases h : ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1
      · simp [h]
      · rw [if_neg h, if_neg h, if_neg h]
        ring
    rw [hsplit, hoff1, h2']
    ring
  -- (E7) the variance identity in `ℤ`, and the classification of the values
  have hvarZ : (∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then (0 : ℤ)
      else mf y * ((Work.CharCore.irrDeg ψ₁ : ℤ) - mf y))) = 0 := by
    apply zinj
    have hcast : (((∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then (0 : ℤ)
        else mf y * ((Work.CharCore.irrDeg ψ₁ : ℤ) - mf y))) : ℤ) : ℂ)
        = ∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then (0 : ℂ)
            else ((mf y * ((Work.CharCore.irrDeg ψ₁ : ℤ) - mf y) : ℤ) : ℂ)) := by
      push_cast
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases h : ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1 <;> simp [h]
    have hpt : ∀ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then (0 : ℂ)
        else ((mf y * ((Work.CharCore.irrDeg ψ₁ : ℤ) - mf y) : ℤ) : ℂ))
        = (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then (0 : ℂ)
            else ψ₁ y * (s - ψ₁ y)) := by
      intro y
      by_cases h : ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, hsN_cast, hmf y (hint y h)]
        push_cast
        ring
    rw [hcast, Finset.sum_congr rfl (fun y _ => hpt y), hvarC]
    simp
  have hterm : ∀ y : W, (¬ ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) →
      mf y * ((Work.CharCore.irrDeg ψ₁ : ℤ) - mf y) = 0 := by
    have hnn : ∀ y : W, 0 ≤ (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then (0 : ℤ)
        else mf y * ((Work.CharCore.irrDeg ψ₁ : ℤ) - mf y)) := by
      intro y
      by_cases h : ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1
      · rw [if_pos h]
      · rw [if_neg h]
        exact mul_nonneg (hbound y h).1 (sub_nonneg.mpr (hbound y h).2)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hnn y)).mp hvarZ
    intro y hy
    have := hall y (Finset.mem_univ y)
    rwa [if_neg hy] at this
  have hmval : ∀ y : W, (¬ ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) →
      mf y = 0 ∨ mf y = (Work.CharCore.irrDeg ψ₁ : ℤ) := by
    intro y hy
    rcases mul_eq_zero.mp (hterm y hy) with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h).symm
  -- (E8) the value of the first moment
  have hsumM : (∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then (0 : ℤ) else mf y))
      = ((Subgroup.normalizer (K : Set W)).index : ℤ) * (Work.CharCore.irrDeg ψ₁ : ℤ) := by
    apply zinj
    have hcast : (((∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then (0 : ℤ)
        else mf y)) : ℤ) : ℂ)
        = ∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then (0 : ℂ)
            else ((mf y : ℤ) : ℂ)) := by
      push_cast
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases h : ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1 <;> simp [h]
    have hcast2 : (∑ y : W, (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then (0 : ℂ)
        else ((mf y : ℤ) : ℂ))) = ((Subgroup.normalizer (K : Set W)).index : ℂ) * s := by
      rw [← hoff1]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases h : ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
        exact (hmf y (hint y h)).symm
    rw [hcast, hcast2, hsN_cast]
    push_cast
    ring
  -- (E9) the count
  have hcardA : (Finset.univ.filter (fun y : W =>
        ¬ (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) ∧ mf y = (Work.CharCore.irrDeg ψ₁ : ℤ))).card
      = (Subgroup.normalizer (K : Set W)).index := by
    set A : Finset W := Finset.univ.filter (fun y : W =>
      ¬ (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) ∧
        mf y = (Work.CharCore.irrDeg ψ₁ : ℤ)) with hA
    have h2 : (∑ y ∈ A, mf y) = ∑ y : W,
        (if (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) then (0 : ℤ) else mf y) := by
      rw [hA, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases h : ∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1
      · rw [if_pos h, if_neg (fun hh => hh.1 h)]
      · rw [if_neg h]
        rcases hmval y h with h0 | hN
        · rw [h0]; split <;> rfl
        · rw [hN, if_pos ⟨h, rfl⟩]
    have h3 : (∑ y ∈ A, mf y) = (A.card : ℤ) * (Work.CharCore.irrDeg ψ₁ : ℤ) := by
      have hsum_eq : (∑ y ∈ A, mf y) = ∑ y ∈ A, (Work.CharCore.irrDeg ψ₁ : ℤ) := by
        refine Finset.sum_congr rfl (fun y hy => ?_)
        rw [hA] at hy
        exact (Finset.mem_filter.mp hy).2.2
      rw [hsum_eq, Finset.sum_const, nsmul_eq_mul]
    have h5 : (A.card : ℤ) * (Work.CharCore.irrDeg ψ₁ : ℤ)
        = ((Subgroup.normalizer (K : Set W)).index : ℤ)
          * (Work.CharCore.irrDeg ψ₁ : ℤ) := by
      rw [← h3, h2, hsumM]
    have hfinal : A.card = (Subgroup.normalizer (K : Set W)).index := by
      exact_mod_cast (mul_right_cancel₀ hsNnz h5)
    exact hfinal
  -- (E10) `π y = |I|` iff `y ∈ ker π`
  have hπI : ((Nat.card I : ℕ) : ℂ)
      = 1 + (T.card : ℂ) * ((Work.CharCore.irrDeg ψ₁ : ℤ) : ℂ) := by
    rw [show ((Nat.card I : ℕ) : ℂ) = ((Nat.card K : ℕ) : ℂ) from by rw [hIK],
      ← hπ1, hπoff 1 hnotY1, hs ψ₁ hψ₁T, hsN_cast]
  have hiff : ∀ y : W, (π y = ((Nat.card I : ℕ) : ℂ)) ↔
      (¬ (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) ∧
        mf y = (Work.CharCore.irrDeg ψ₁ : ℤ)) := by
    intro y
    constructor
    · intro hpy
      have hyY : ¬ (∃ x : W, x⁻¹ * y * x ∈ K ∧ y ≠ 1) := by
        intro hY
        have h0 : ((Nat.card I : ℕ) : ℂ) = 0 := by rw [← hpy]; exact hπY y hY
        have hIp : ((Nat.card I : ℕ) : ℂ) ≠ 0 := by
          rw [Nat.cast_ne_zero]
          exact Nat.pos_iff_ne_zero.mp (by
            rw [Nat.card_eq_fintype_card]; exact Fintype.card_pos)
        exact hIp h0
      refine ⟨hyY, ?_⟩
      have hs_eq : ψ₁ y = s := by
        have h1 : ((Nat.card I : ℕ) : ℂ) = 1 + (T.card : ℂ) * ψ₁ y := by
          rw [← hpy]; exact hπoff y hyY
        have h2 : ((Nat.card I : ℕ) : ℂ) = 1 + (T.card : ℂ) * s := by
          rw [show ((Nat.card I : ℕ) : ℂ) = ((Nat.card K : ℕ) : ℂ) from by rw [hIK],
            ← hπ1, hπoff 1 hnotY1, hs ψ₁ hψ₁T]
        have h3 : 1 + (T.card : ℂ) * ψ₁ y = 1 + (T.card : ℂ) * s := by rw [← h1, h2]
        exact mul_left_cancel₀ hTcard (by linear_combination h3)
      apply zinj
      rw [← hmf y (hint y hyY), hs_eq, hsN_cast]
    · rintro ⟨hyY, hm⟩
      have hm_eq : ψ₁ y = ((Work.CharCore.irrDeg ψ₁ : ℤ) : ℂ) := by
        rw [← hm]
        exact hmf y (hint y hyY)
      rw [hπoff y hyY, hm_eq, ← hπI]
  have hkerF : ∀ y : W, (π y = ((Nat.card I : ℕ) : ℂ)) ↔
      y ∈ (MulAction.toPermHom W I).ker := by
    intro y
    constructor
    · intro hpy
      have hcard : Nat.card (MulAction.fixedBy I y) = Nat.card I := by
        have h := hfix y
        rw [h] at hpy
        exact_mod_cast hpy
      have hcardf : Fintype.card (MulAction.fixedBy I y) = Fintype.card I := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
        exact hcard
      have huniv : Fintype.card (Set.univ : Set I) = Fintype.card I := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
        exact Nat.card_congr (Equiv.Set.univ I)
      have hset : MulAction.fixedBy I y = (Set.univ : Set I) :=
        Set.eq_of_subset_of_card_le (fun _ _ => Set.mem_univ _) (by rw [huniv, ← hcardf])
      have hfixall : ∀ i : I, y • i = i := fun i => by
        have h : i ∈ MulAction.fixedBy I y := by rw [hset]; exact Set.mem_univ i
        simpa using h
      rw [MonoidHom.mem_ker]
      ext i
      simpa [MulAction.toPermHom_apply, MulAction.toPerm_apply] using hfixall i
    · intro hy
      have hfixall : ∀ i : I, y • i = i := fun i => by
        have h := congrArg (fun f : Equiv.Perm I => f i) (MonoidHom.mem_ker.mp hy)
        simpa [MulAction.toPermHom_apply, MulAction.toPerm_apply] using h
      have hset : MulAction.fixedBy I y = (Set.univ : Set I) := by
        rw [Set.eq_univ_iff_forall]
        intro i
        rw [MulAction.mem_fixedBy]
        exact hfixall i
      rw [hfix y, hset, Nat.card_congr (Equiv.Set.univ I)]
  have hcardKer : (Finset.univ.filter (fun y : W => y ∈ (MulAction.toPermHom W I).ker)).card
      = (Subgroup.normalizer (K : Set W)).index := by
    rw [← hcardA]
    congr 1
    refine Finset.filter_congr (s := Finset.univ) (fun y _ => ?_)
    exact (hkerF y).symm.trans (hiff y)
  -- ═══ conclusion ═══
  have hcard_mul : Nat.card ↥((MulAction.toPermHom W I).ker)
      * Nat.card ↥(Subgroup.normalizer (K : Set W)) = Nat.card W := by
    have h1 : Nat.card ↥((MulAction.toPermHom W I).ker)
        = (Subgroup.normalizer (K : Set W)).index := by
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_ofFinset _
        (fun y => by simp only [Finset.mem_filter, Finset.mem_univ, true_and, SetLike.mem_coe])).trans hcardKer
    rw [h1, Subgroup.index_mul_card]
  exact sup_eq_top_of_card_mul (ker_inf_normalizer_eq_bot hI hreg hcent) hcard_mul

/-- **Peterfalvi I Appendix VI** (pp. 213–215), a generalisation of Burnside's result on
permutation groups of prime degree.  If `W` acts on a set `I` with `1 < |I|`, and `K ≤ W` acts
*regularly* on `I` (sharply transitively) with `C_W(k) = K` for every `k ∈ K#`, then either `W`
acts doubly transitively on `I`, or `W = C_W(I)·N_W(K)`.

This is the input of Ch. III §3 Prop. 2 (p.178).  Under the hypotheses `K` is a T.I.F.N. subgroup
of `W` (Isaacs, *Character Theory of Finite Groups*, Definition 7.16: `K` is a T.I. set,
`K ⊴ N_W(K)`, `C_W(k) ≤ K` for `1 ≠ k ∈ K`), the action is equivalent to the action on the cosets
of `N_W(K)`, and the proof runs through Suzuki's theory of exceptional characters for T.I.F.N.
subgroups (Isaacs 7.17–7.20: the set `𝒮 = {χ ∈ Irr(N_W(K)) | K ⊄ ker χ}` is coherent, the isometry
`Ind : ℤ[𝒮] → ℤ[Irr(W)]` of exceptional characters, the `|W : N_W(K)|` exceptional characters
constant off `K#`, and the variance identity `Σ i(s-i)nᵢ = 0`).  In the application the permutation
character is `π = 1_W + ψ₁ + … + ψ_t`, and if `t ≥ 2` and `N_W(K) ≠ K` then the `ψᵢ` are the
exceptional characters.

Available character-theory machinery in the workspace: `Submission.Work.Coherence`
(`Coherent`, `cfInner`, isometry extension), `Submission.Work.Clifford` (Clifford
correspondence, `Irr` as a `Finset`, Galois action on `Irr`), `Submission.Work.Induction`
(`indFun`, Frobenius reciprocity, `cfInner_indFun_eq_of_TI`), `Submission.Work.Frobenius.Char`
(irreducibility and orthonormality of `Irr`), and `Submission.Work.CharCore` (`irr_orthonormal`,
`classFun_eq_sum_irr`). -/
theorem appVI {W : Type*} [Group W] [Finite W] {I : Type*} [Fintype I] [MulAction W I]
    {K : Subgroup W} (hI : 1 < Fintype.card I)
    (hreg : ∀ i j : I, ∃! k : K, (k : W) • i = j)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) = K) :
    MulAction.IsMultiplyPretransitive W I 2 ∨
      (MulAction.toPermHom W I).ker ⊔ Subgroup.normalizer (K : Set W) = ⊤ := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  exact appVI_fintype hI hreg hcent

end Work.NormalComplement

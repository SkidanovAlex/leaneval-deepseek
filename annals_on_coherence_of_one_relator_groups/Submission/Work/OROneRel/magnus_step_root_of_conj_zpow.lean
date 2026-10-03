import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.not_isProperPower_of
import Submission.Work.OROneRel.relatorNorm_of_zpow

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The inverse of a proper power is a proper power, and conversely. -/
theorem isProperPower_inv_iff (r : FreeGroup α) : IsProperPower r⁻¹ ↔ IsProperPower r := by
  constructor
  · rintro ⟨z, m, hm, hz⟩
    exact ⟨z⁻¹, m, hm, by rw [← inv_inv r, hz, inv_pow]⟩
  · rintro ⟨z, m, hm, hz⟩
    exact ⟨z⁻¹, m, hm, by rw [hz, inv_pow]⟩

/-- A generator, or the inverse of a generator, is not a proper power. -/
theorem not_isProperPower_of_zpow_of_eq_one_or_neg_one (a : α) {k : ℤ}
    (hk : k = 1 ∨ k = -1) : ¬ IsProperPower ((FreeGroup.of a : FreeGroup α) ^ k) := by
  rcases hk with rfl | rfl
  · rw [zpow_one]; exact not_isProperPower_of a
  · rw [zpow_neg_one]
    exact fun h => not_isProperPower_of a ((isProperPower_inv_iff (FreeGroup.of a)).mp h)

/-- Powers of a conjugate: `(c * w * c⁻¹) ^ n = c * w ^ n * c⁻¹`. -/
theorem conj_pow_eq_freeGroup (c w : FreeGroup α) (n : ℕ) :
    (c * w * c⁻¹) ^ n = c * w ^ n * c⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, ih]; group

/-- If `α` has only the generator `a`, then any word conjugate to `of a ^ k` (`k = ±1`) has relator
norm `1`; consequently `relatorNorm u ≥ 2` forces a second generator to exist. -/
theorem exists_ne_of_conj_of_zpow (a : α) (k : ℤ) (hk : k = 1 ∨ k = -1) (c u : FreeGroup α)
    (h : u = c * FreeGroup.of a ^ k * c⁻¹) (hn : 2 ≤ relatorNorm u) : ∃ b : α, b ≠ a := by
  classical
  by_contra hno
  have hno' : ∀ b : α, b = a := by
    intro b
    by_contra hbb
    exact hno ⟨b, hbb⟩
  have hrange : Set.range (FreeGroup.of : α → FreeGroup α) = {FreeGroup.of a} := by
    ext x; constructor
    · rintro ⟨b, rfl⟩; exact congrArg FreeGroup.of (hno' b)
    · rintro (rfl : x = FreeGroup.of a); exact ⟨a, rfl⟩
  have htop : Subgroup.zpowers (FreeGroup.of a : FreeGroup α) = ⊤ := by
    rw [Subgroup.zpowers_eq_closure, ← hrange]
    exact FreeGroup.closure_range_of α
  have hc : c ∈ Subgroup.zpowers (FreeGroup.of a : FreeGroup α) := by
    rw [htop]; exact Subgroup.mem_top c
  obtain ⟨n, hn'⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hu : u = FreeGroup.of a ^ k := by
    rw [h, ← hn',
      show (FreeGroup.of a ^ n)⁻¹ = FreeGroup.of a ^ (-n) from (zpow_neg _ _).symm,
      ← zpow_add, ← zpow_add]
    congr 1
    ring
  have hnorm : relatorNorm u = 1 := by
    rw [hu, relatorNorm_of_zpow]
    rcases hk with rfl | rfl <;> norm_num
  omega

set_option linter.unusedVariables false in
theorem magnus_step_root_of_conj_zpow {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (a : α) (k : ℤ) (hk : k = 1 ∨ k = -1) (c : FreeGroup α)
    (h : u = c * FreeGroup.of a ^ k * c⁻¹) (hn : 2 ≤ relatorNorm u) :
    ∃ (β : Type u) (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v ∧
      Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm u ∧
      ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
        (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
        ∃ c' : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
            c' * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c'⁻¹ := by
  classical
  obtain ⟨b, hba⟩ := exists_ne_of_conj_of_zpow a k hk c u h hn
  have hab : a ≠ b := fun hh => hba hh.symm
  let β : Type u := {x : α // x ≠ b}
  let v : FreeGroup β := FreeGroup.of (⟨a, hab⟩ : β) ^ k
  let H : Type u := PresentedGroup ({v ^ l} : Set (FreeGroup β))
  let φ : (⊥ : Subgroup H) ≃* (⊥ : Subgroup H) := MulEquiv.refl _
  let M : Type u := HNNExtension H ⊥ ⊥ φ
  let f : α → M := fun x => if hx : x = b then HNNExtension.t
      else HNNExtension.of (PresentedGroup.of (⟨x, hx⟩ : β))
  have hfa1 : (FreeGroup.lift f) (FreeGroup.of a ^ k) =
      (HNNExtension.of (PresentedGroup.of (⟨a, hab⟩ : β)) : M) ^ k := by
    rw [map_zpow, FreeGroup.lift_apply_of]
    congr 1
    dsimp only [f]
    rw [dif_neg hab]
  have hfa2 : (HNNExtension.of (PresentedGroup.of (⟨a, hab⟩ : β)) : M) ^ k =
      HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) := by
    calc (HNNExtension.of (PresentedGroup.of (⟨a, hab⟩ : β)) : M) ^ k
        = HNNExtension.of ((PresentedGroup.of (⟨a, hab⟩ : β) : H) ^ k) :=
          (map_zpow HNNExtension.of (PresentedGroup.of (⟨a, hab⟩ : β)) k).symm
      _ = HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) := by
          rw [show (PresentedGroup.of (⟨a, hab⟩ : β) : H) =
                (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β))) (FreeGroup.of (⟨a, hab⟩ : β))
                from rfl,
              (map_zpow (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)))
                (FreeGroup.of (⟨a, hab⟩ : β)) k).symm]
  have hfa : (FreeGroup.lift f) (FreeGroup.of a ^ k) =
      HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) :=
    hfa1.trans hfa2
  have hvpow :
      (HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) : M) ^ l = 1 := by
    calc (HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) : M) ^ l
        = HNNExtension.of ((PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) ^ l) :=
          (map_pow HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) l).symm
      _ = HNNExtension.of 1 := by
          rw [(map_pow (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β))) v l).symm,
            PresentedGroup.one_of_mem (Set.mem_singleton (v ^ l))]
      _ = 1 := map_one _
  have hfu : (FreeGroup.lift f) (u ^ l) = 1 := by
    rw [show u ^ l = c * (FreeGroup.of a ^ k) ^ l * c⁻¹ from by rw [h, conj_pow_eq_freeGroup],
      map_mul, map_mul, map_pow, map_inv, hfa, hvpow, mul_one]
    exact mul_inv_cancel _
  have hf : ∀ r ∈ ({u ^ l} : Set (FreeGroup α)), FreeGroup.lift f r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    exact hfu
  let Φ : PresentedGroup ({u ^ l} : Set (FreeGroup α)) →* M :=
    PresentedGroup.toGroup (f := f) hf
  have hΦof : ∀ x : α, Φ (PresentedGroup.of x) = f x := fun x => PresentedGroup.toGroup.of hf
  have hΦmk : ∀ y : FreeGroup α,
      Φ (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) y) = FreeGroup.lift f y := by
    intro y
    have hcomp : Φ.comp (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))) = FreeGroup.lift f := by
      apply FreeGroup.ext_hom
      intro x
      rw [MonoidHom.comp_apply]
      change Φ (PresentedGroup.of x) = FreeGroup.lift f (FreeGroup.of x)
      rw [hΦof x, FreeGroup.lift_apply_of]
    have := DFunLike.congr_fun hcomp y
    simpa only [MonoidHom.comp_apply] using this
  have hX : ((PresentedGroup.of a : PresentedGroup ({u ^ l} : Set (FreeGroup α))) ^ k) ^ l = 1 := by
    have hone : (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) ^ l = 1 :=
      PresentedGroup.one_of_mem (Set.mem_singleton (u ^ l))
    have hexp : (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) ^ l =
        (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) c) *
          (((PresentedGroup.of a : PresentedGroup ({u ^ l} : Set (FreeGroup α))) ^ k) ^ l) *
          (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) c)⁻¹ := by
      calc (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) ^ l
          = (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))) (u ^ l) :=
            (map_pow (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))) u l).symm
        _ = (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)))
              (c * (FreeGroup.of a ^ k) ^ l * c⁻¹) := by
            rw [show u ^ l = c * (FreeGroup.of a ^ k) ^ l * c⁻¹ from by rw [h, conj_pow_eq_freeGroup]]
        _ = (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) c) *
              ((PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))) ((FreeGroup.of a ^ k) ^ l)) *
              (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) c)⁻¹ := by
            rw [map_mul, map_mul, map_pow, map_inv]
        _ = (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) c) *
              (((PresentedGroup.of a : PresentedGroup ({u ^ l} : Set (FreeGroup α))) ^ k) ^ l) *
              (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) c)⁻¹ := by
            rw [map_pow, map_zpow]
            rfl
    have hconj : (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) c) *
          (((PresentedGroup.of a : PresentedGroup ({u ^ l} : Set (FreeGroup α))) ^ k) ^ l) *
          (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) c)⁻¹ = 1 := by
      rw [← hexp, hone]
    calc (((PresentedGroup.of a : PresentedGroup ({u ^ l} : Set (FreeGroup α))) ^ k) ^ l)
        = (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) c)⁻¹ *
            ((PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) c) *
              (((PresentedGroup.of a : PresentedGroup ({u ^ l} : Set (FreeGroup α))) ^ k) ^ l) *
              (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) c)⁻¹) *
            (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) c) := by group
      _ = (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) c)⁻¹ * 1 *
            (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) c) := by rw [hconj]
      _ = 1 := by group
  let g : β → PresentedGroup ({u ^ l} : Set (FreeGroup α)) := fun z => PresentedGroup.of (z : α)
  have hψrel : ∀ r ∈ ({v ^ l} : Set (FreeGroup β)), FreeGroup.lift g r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    have hv : (FreeGroup.lift g) (v ^ l) =
        ((PresentedGroup.of a : PresentedGroup ({u ^ l} : Set (FreeGroup α))) ^ k) ^ l := by
      calc (FreeGroup.lift g) (v ^ l)
          = ((FreeGroup.lift g) v) ^ l := map_pow _ _ _
        _ = ((PresentedGroup.of a : PresentedGroup ({u ^ l} : Set (FreeGroup α))) ^ k) ^ l := by
            rw [show v = FreeGroup.of (⟨a, hab⟩ : β) ^ k from rfl, map_zpow,
              FreeGroup.lift_apply_of]
    rw [hv]; exact hX
  let ψH : H →* PresentedGroup ({u ^ l} : Set (FreeGroup α)) :=
    PresentedGroup.toGroup (f := g) hψrel
  have hψof : ∀ z : β, ψH (PresentedGroup.of z) = PresentedGroup.of (z : α) :=
    fun z => PresentedGroup.toGroup.of hψrel
  have hx : ∀ aa : (⊥ : Subgroup H),
      (PresentedGroup.of b : PresentedGroup ({u ^ l} : Set (FreeGroup α))) * ψH ↑aa =
        ψH ↑(φ aa) * (PresentedGroup.of b : PresentedGroup ({u ^ l} : Set (FreeGroup α))) := by
    intro aa
    have h1 : ((aa : (⊥ : Subgroup H)) : H) = 1 := Subgroup.mem_bot.mp aa.2
    have h2 : ((φ aa : (⊥ : Subgroup H)) : H) = 1 := Subgroup.mem_bot.mp (φ aa).2
    rw [h1, h2]
    simp
  let Ψ : M →* PresentedGroup ({u ^ l} : Set (FreeGroup α)) :=
    HNNExtension.lift ψH (PresentedGroup.of b) hx
  have hΨof : Ψ.comp HNNExtension.of = ψH :=
    MonoidHom.ext (fun gg => HNNExtension.lift_of ψH (PresentedGroup.of b) hx gg)
  have hΨt : Ψ HNNExtension.t =
      (PresentedGroup.of b : PresentedGroup ({u ^ l} : Set (FreeGroup α))) :=
    HNNExtension.lift_t ψH (PresentedGroup.of b) hx
  have hΦψH : Φ.comp ψH = HNNExtension.of := by
    apply PresentedGroup.ext
    intro z
    show Φ (ψH (PresentedGroup.of z)) = HNNExtension.of (PresentedGroup.of z)
    rw [hψof z, hΦof (z : α)]
    show (if hx' : (z : α) = b then HNNExtension.t
        else HNNExtension.of (PresentedGroup.of (⟨(z : α), hx'⟩ : β))) =
      HNNExtension.of (PresentedGroup.of z)
    rw [dif_neg z.2]
  have hΦΨ : Φ.comp Ψ = MonoidHom.id M := by
    apply HNNExtension.hom_ext
    · show (Φ.comp Ψ).comp HNNExtension.of = (MonoidHom.id M).comp HNNExtension.of
      rw [MonoidHom.comp_assoc, hΨof, MonoidHom.id_comp]
      exact hΦψH
    · show (Φ.comp Ψ) HNNExtension.t = (MonoidHom.id M) HNNExtension.t
      rw [MonoidHom.comp_apply, hΨt, MonoidHom.id_apply, hΦof b]
      show f b = HNNExtension.t
      dsimp only [f]
      rw [dif_pos rfl]
  have hΨΦ : Ψ.comp Φ = MonoidHom.id (PresentedGroup ({u ^ l} : Set (FreeGroup α))) := by
    apply PresentedGroup.ext
    intro x
    show Ψ (Φ (PresentedGroup.of x)) = PresentedGroup.of x
    rw [hΦof x]
    by_cases hxb : x = b
    · subst hxb
      dsimp only [f]
      rw [dif_pos rfl, hΨt]
    · dsimp only [f]
      rw [dif_neg hxb]
      rw [show Ψ (HNNExtension.of (PresentedGroup.of (⟨x, hxb⟩ : β))) =
            ψH (PresentedGroup.of (⟨x, hxb⟩ : β)) from HNNExtension.lift_of _ _ _ _]
      rw [hψof (⟨x, hxb⟩ : β)]
  let e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃* M :=
    MonoidHom.toMulEquiv Φ Ψ hΨΦ hΦΨ
  refine ⟨β, v, ?_, ?_, ⊥, ⊥, φ, e, e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) c), ?_⟩
  · exact not_isProperPower_of_zpow_of_eq_one_or_neg_one (⟨a, hab⟩ : β) hk
  · have hv1 : relatorNorm v = 1 := by
      rw [show v = FreeGroup.of (⟨a, hab⟩ : β) ^ k from rfl, relatorNorm_of_zpow]
      rcases hk with rfl | rfl <;> norm_num
    omega
  · have hL : e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
        FreeGroup.lift f c *
          HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) *
          (FreeGroup.lift f c)⁻¹ := by
      rw [show e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
            Φ (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) from rfl,
        hΦmk u, h, map_mul, map_mul, map_inv, hfa]
    have hR : e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) c) = FreeGroup.lift f c := by
      rw [show e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) c) =
            Φ (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) c) from rfl, hΦmk c]
    rw [hL, hR]

end Work.OROneRel

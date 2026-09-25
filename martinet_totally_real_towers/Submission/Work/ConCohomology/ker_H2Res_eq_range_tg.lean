import Mathlib
import Submission.Work.ConCohomology.Extension
import Submission.Work.ConCohomology.q_pullback_tgFun_is_coboundary
import Submission.Work.ConCohomology.pullback_coboundary_iff_exists_invariant_cocycle

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.ConCohomology

open Function Classical

section Aux

variable {G Q N : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable [Group N] [TopologicalSpace N] [IsTopologicalGroup N]

/-- The bundled transgression cochain of a `1`-cochain on `N` is the raw transgression
`tgFun` of its underlying function. -/
lemma tgCochain_coe {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    [DistribMulAction Q M] [DistribMulAction N M] [IsDiscreteGModule Q M]
    (E : GroupExt G Q N) (s : Q → G) (hs : ∀ y : Q, E.q (s y) = y)
    (hscont : Continuous s)
    (hkcont : Continuous fun p : {x : G // E.q x = 1} => E.kerLift p.1 p.2)
    (φ : Cochain1 N M) :
    (tgCochain E s hs hscont hkcont φ : Q × Q → M) = tgFun E s hs (φ : N → M) := rfl

/-- For a locally constant `1`-cochain `φ` on `N`, the function `x ↦ φ (liftArg E s hs x)` on `G`
is locally constant, provided the section `s` is continuous and the kernel lifting is continuous
on `ker q`. -/
lemma isLocallyConstant_comp_liftArg {M : Type*} [AddCommGroup M] [DistribMulAction N M]
    [IsDiscreteGModule N M]
    (E : GroupExt G Q N) (hq : Continuous E.q) (s : Q → G)
    (hs : ∀ y : Q, E.q (s y) = y) (hscont : Continuous s)
    (hkcont : Continuous fun p : {x : G // E.q x = 1} => E.kerLift p.1 p.2)
    (φ : Cochain1 N M) :
    IsLocallyConstant fun x : G => φ (liftArg E s hs x) := by
  have hmem : ∀ x : G, E.q (x * (s (E.q x))⁻¹) = 1 := fun x => by
    rw [map_mul, map_inv, hs]; simp
  have hcont : Continuous fun x : G =>
      (⟨x * (s (E.q x))⁻¹, hmem x⟩ : {x : G // E.q x = 1}) :=
    (continuous_id.mul (hscont.comp hq).inv).subtype_mk hmem
  have hgood : IsLocallyConstant fun x : G =>
      φ ((fun p : {x : G // E.q x = 1} => E.kerLift p.1 p.2)
        (⟨x * (s (E.q x))⁻¹, hmem x⟩ : {x : G // E.q x = 1})) :=
    φ.isLocallyConstant.comp_continuous (hkcont.comp hcont)
  have heq : (fun x : G => φ (liftArg E s hs x))
      = fun x : G => φ ((fun p : {x : G // E.q x = 1} => E.kerLift p.1 p.2)
        (⟨x * (s (E.q x))⁻¹, hmem x⟩ : {x : G // E.q x = 1})) := by
    funext x
    congr 1
  rw [heq]
  exact hgood

end Aux

theorem ker_H2Res_eq_range_tg {G Q N : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [Group N] [TopologicalSpace N] [IsTopologicalGroup N] {M : Type*} [AddCommGroup M]
    [DistribMulAction G M] [DistribMulAction N M] [DistribMulAction Q M]
    [IsDiscreteGModule G M] [IsDiscreteGModule N M] [IsDiscreteGModule Q M]
    (E : GroupExt G Q N) (hq : Continuous E.q) (hi : Continuous E.i)
    (hcompN : ∀ (n : N) (m : M), n • m = m)
    (hcompG : ∀ (g : G) (m : M), g • m = E.q g • m) (s : Q → G)
    (hs : ∀ y : Q, E.q (s y) = y) (hscont : Continuous s)
    (hkcont : Continuous fun p : {x : G // E.q x = 1} => E.kerLift p.1 p.2)
    (z : Z2 Q M) :
    H2Res E.q hq hcompG (H2.mk z) = 0 ↔
      ∃ (φ : Z1 N M) (_hφ : IsCocycle1 (φ : N → M))
        (_hinv : ∀ (g : G) (n : N), (φ : N → M) (E.conj g n) = g • (φ : N → M) n),
        ∃ w : Cochain1 Q M,
          ((tgCochain E s hs hscont hkcont φ : Q × Q → M) - (z.1 : Q × Q → M)) =
            d1Fun (G := Q) (w : Q → M) := by
  have hqi : ∀ n : N, E.q (E.i n) = 1 := fun n => (E.ker_eq (E.i n)).mpr ⟨n, rfl⟩
  have hcompQ : ∀ (y : Q) (m : M), y • m = s y • m := by
    intro y m
    calc y • m = E.q (s y) • m := by rw [hs y]
      _ = s y • m := (hcompG (s y) m).symm
  rw [H2Res_mk, H2.mk_eq_zero_iff, mem_B2', mem_B2]
  constructor
  · -- (⇒): the class of `z` is killed by inflation, hence `z` is the transgression of an
    -- invariant `1`-cocycle on `N`, up to a coboundary on `Q`.
    rintro ⟨b, hb⟩
    have hb' : ∀ x y : G, (z : Cochain2 Q M) (E.q x, E.q y) =
        x • (b : G → M) y - (b : G → M) (x * y) + (b : G → M) x := by
      intro x y
      have h1 := congrFun (congrArg (fun f : Cochain2 G M => (f : G × G → M)) hb) (x, y)
      rw [Z2Res_coe, cochain2Res_apply] at h1
      exact h1.symm
    have hc1 : ∀ y : Q, (z : Cochain2 Q M) (1, y) = (b : G → M) 1 := by
      intro y
      have h := hb' 1 (s y)
      rw [map_one, hs y, one_smul, one_mul] at h
      rw [h, sub_self, zero_add]
    have hii : ∀ m n : N, (b : G → M) (E.i m * E.i n) =
        (b : G → M) (E.i n) - (b : G → M) 1 + (b : G → M) (E.i m) := by
      intro m n
      have h := hb' (E.i m) (E.i n)
      rw [hqi m, hqi n, hc1 1, hcompG (E.i m) ((b : G → M) (E.i n)), hqi m, one_smul] at h
      rw [h]
      abel
    have hφf_loc : IsLocallyConstant (fun n : N => (b : G → M) 1 - (b : G → M) (E.i n)) := by
      have h1 : IsLocallyConstant (fun _ : N => (b : G → M) 1) := IsLocallyConstant.const _
      have h2 : IsLocallyConstant (fun n : N => (b : G → M) (E.i n)) :=
        b.isLocallyConstant.comp_continuous hi
      exact h1.sub h2
    have hφf_coc : IsCocycle1 (fun n : N => (b : G → M) 1 - (b : G → M) (E.i n)) := by
      intro m n
      show (b : G → M) 1 - (b : G → M) (E.i (m * n)) =
        ((b : G → M) 1 - (b : G → M) (E.i m)) +
          m • ((b : G → M) 1 - (b : G → M) (E.i n))
      rw [map_mul, hii m n, hcompN m ((b : G → M) 1 - (b : G → M) (E.i n))]
      abel
    have hφf_inv : ∀ (g : G) (n : N),
        (fun n : N => (b : G → M) 1 - (b : G → M) (E.i n)) (E.conj g n) =
          g • (fun n : N => (b : G → M) 1 - (b : G → M) (E.i n)) n := by
      intro g n
      show (b : G → M) 1 - (b : G → M) (E.i (E.conj g n)) =
        g • ((b : G → M) 1 - (b : G → M) (E.i n))
      have h1 : (b : G → M) (E.i n * g⁻¹) =
          (b : G → M) g⁻¹ - (b : G → M) 1 + (b : G → M) (E.i n) := by
        have h := hb' (E.i n) g⁻¹
        rw [hqi n, map_inv] at h
        rw [hc1 ((E.q g)⁻¹), hcompG (E.i n) ((b : G → M) g⁻¹), hqi n, one_smul] at h
        rw [h]
        abel
      have h2 : (b : G → M) (g * (E.i n * g⁻¹)) =
          g • (b : G → M) (E.i n * g⁻¹) - (z : Cochain2 Q M) (E.q g, (E.q g)⁻¹)
            + (b : G → M) g := by
        have h := hb' g (E.i n * g⁻¹)
        rw [map_mul, hqi n, map_inv, one_mul] at h
        rw [h]
        abel
      have h3 : (b : G → M) 1 =
          g • (b : G → M) g⁻¹ - (z : Cochain2 Q M) (E.q g, (E.q g)⁻¹) + (b : G → M) g := by
        have h := hb' g g⁻¹
        rw [map_inv, mul_inv_cancel] at h
        rw [h]
        abel
      have hA : (b : G → M) (g * (E.i n * g⁻¹)) =
          (b : G → M) 1 - g • (b : G → M) 1 + g • (b : G → M) (E.i n) := by
        calc (b : G → M) (g * (E.i n * g⁻¹))
            = g • ((b : G → M) g⁻¹ - (b : G → M) 1 + (b : G → M) (E.i n))
                - (z : Cochain2 Q M) (E.q g, (E.q g)⁻¹) + (b : G → M) g := by rw [h2, h1]
          _ = (g • (b : G → M) g⁻¹ - (z : Cochain2 Q M) (E.q g, (E.q g)⁻¹) + (b : G → M) g)
                + (g • (b : G → M) (E.i n) - g • (b : G → M) 1) := by
                rw [smul_add, smul_sub]
                abel
          _ = (b : G → M) 1 - g • (b : G → M) 1 + g • (b : G → M) (E.i n) := by
                rw [h3]
                abel
      rw [E.i_conj, mul_assoc, hA, smul_sub]
      abel
    have hwf_loc : IsLocallyConstant (fun y : Q => -((b : G → M) (s y))) :=
      (b.isLocallyConstant.comp_continuous hscont).neg
    have hwf_eq :
        tgFun E s hs (fun n : N => (b : G → M) 1 - (b : G → M) (E.i n)) - (z : Cochain2 Q M)
          = d1Fun (G := Q) (fun y : Q => -((b : G → M) (s y))) := by
      funext p
      obtain ⟨y1, y2⟩ := p
      have hkey' : ∀ a zz : G, E.q a = E.q zz →
          (b : G → M) 1 - (b : G → M) (a * zz⁻¹) + (b : G → M) a = (b : G → M) zz := by
        intro a zz hqz
        have hA : (b : G → M) (a * zz⁻¹) =
            a • (b : G → M) zz⁻¹ - (z : Cochain2 Q M) (E.q zz, (E.q zz)⁻¹)
              + (b : G → M) a := by
          have h := hb' a zz⁻¹
          rw [map_inv, hqz] at h
          rw [h]
          abel
        have hB : (b : G → M) zz =
            (b : G → M) 1 - zz • (b : G → M) zz⁻¹
              + (z : Cochain2 Q M) (E.q zz, (E.q zz)⁻¹) := by
          have h := hb' zz zz⁻¹
          rw [map_inv, mul_inv_cancel] at h
          rw [h]
          abel
        have hsmul : a • (b : G → M) zz⁻¹ = zz • (b : G → M) zz⁻¹ := by
          rw [hcompG a, hcompG zz, hqz]
        rw [hA, hB, hsmul]
        abel
      have hfin : (b : G → M) 1
          - (b : G → M) (s y1 * s y2 * (s (y1 * y2))⁻¹) + (b : G → M) (s y1 * s y2)
          = (b : G → M) (s (y1 * y2)) :=
        hkey' (s y1 * s y2) (s (y1 * y2)) (by rw [map_mul, hs y1, hs y2, hs (y1 * y2)])
      have hc_s : (z : Cochain2 Q M) (y1, y2) =
          s y1 • (b : G → M) (s y2) - (b : G → M) (s y1 * s y2) + (b : G → M) (s y1) := by
        have h := hb' (s y1) (s y2)
        rwa [hs y1, hs y2] at h
      simp only [Pi.sub_apply, tgFun_eq_tgArg]
      rw [i_tgArg E s hs y1 y2, d1Fun_apply, hc_s, hcompG (s y1) ((b : G → M) (s y2)), hs y1,
        smul_neg, ← hfin]
      abel
    refine ⟨⟨⟨fun n : N => (b : G → M) 1 - (b : G → M) (E.i n), hφf_loc⟩,
      mem_Z1.mpr hφf_coc⟩, hφf_coc, hφf_inv,
      ⟨⟨fun y : Q => -((b : G → M) (s y)), hwf_loc⟩, ?_⟩⟩
    exact hwf_eq
  · -- (⇐): a transgression differing from `z` by a coboundary exhibits `z` as a coboundary
    -- after inflation.
    rintro ⟨φ, hφ, hinv, w, hw⟩
    have hW : ∀ x y : Q, (φ : N → M) (tgArg E s hs x y) - (z : Cochain2 Q M) (x, y)
        = d1Fun (G := Q) (w : Q → M) (x, y) := by
      intro x y
      have h := congrFun hw (x, y)
      simp only [Pi.sub_apply] at h
      rw [tgCochain_coe, tgFun_eq_tgArg] at h
      exact h
    have hgloc : IsLocallyConstant
        (fun x : G => -((φ : N → M) (liftArg E s hs x)) - (w : Q → M) (E.q x)) := by
      have h1 : IsLocallyConstant (fun x : G => (φ : N → M) (liftArg E s hs x)) :=
        isLocallyConstant_comp_liftArg E hq s hs hscont hkcont (φ : Cochain1 N M)
      have h2 : IsLocallyConstant (fun x : G => (w : Q → M) (E.q x)) :=
        w.isLocallyConstant.comp_continuous hq
      exact h1.neg.sub h2
    have hpoint : ∀ x y : G, d1Fun (G := G)
        (fun x : G => -((φ : N → M) (liftArg E s hs x)) - (w : Q → M) (E.q x)) (x, y)
        = (z : Cochain2 Q M) (E.q x, E.q y) := by
      intro x y
      have hφcoc := mem_Z1.mp φ.2
      have hφadd : ∀ a b : N, (φ : N → M) (a * b) = (φ : N → M) a + (φ : N → M) b :=
        fun a b => by rw [hφcoc a b, hcompN a ((φ : N → M) b)]
      have hφ1 : (φ : N → M) 1 = 0 := by
        have h := hφadd 1 1
        rw [mul_one] at h
        exact (add_left_cancel (show (φ : N → M) 1 + 0 = (φ : N → M) 1 + (φ : N → M) 1 by
          rw [add_zero]; exact h)).symm
      have hφinv : ∀ a : N, (φ : N → M) a⁻¹ = -((φ : N → M) a) := by
        intro a
        have h : (φ : N → M) a + (φ : N → M) a⁻¹ = 0 := by
          rw [← hφadd a a⁻¹, mul_inv_cancel, hφ1]
        exact eq_neg_of_add_eq_zero_right h
      have hφadd3 : ∀ a b c : N, (φ : N → M) (a * b * c)
          = (φ : N → M) a + (φ : N → M) b + (φ : N → M) c := by
        intro a b c
        rw [hφadd (a * b) c, hφadd a b]
      have hkey : tgArg E s hs (E.q x) (E.q y)
          = (liftArg E s hs x)⁻¹ * (E.conj x (liftArg E s hs y))⁻¹
            * liftArg E s hs (x * y) := by
        apply E.injective_i
        simp only [i_tgArg, map_mul, map_inv, E.i_conj, i_liftArg]
        group
      have htg : (φ : N → M) (tgArg E s hs (E.q x) (E.q y))
          = -(x • (φ : N → M) (liftArg E s hs y)) + (φ : N → M) (liftArg E s hs (x * y))
            - (φ : N → M) (liftArg E s hs x) := by
        rw [hkey, hφadd3, hφinv, hφinv, hinv x (liftArg E s hs y)]
        abel
      have h1 : d1Fun (G := G)
          (fun x : G => -((φ : N → M) (liftArg E s hs x)) - (w : Q → M) (E.q x)) (x, y)
          = (-(x • (φ : N → M) (liftArg E s hs y)) + (φ : N → M) (liftArg E s hs (x * y))
              - (φ : N → M) (liftArg E s hs x))
            - (x • (w : Q → M) (E.q y) - (w : Q → M) (E.q (x * y)) + (w : Q → M) (E.q x)) := by
        show x • (-((φ : N → M) (liftArg E s hs y)) - (w : Q → M) (E.q y))
            - (-((φ : N → M) (liftArg E s hs (x * y))) - (w : Q → M) (E.q (x * y)))
            + (-((φ : N → M) (liftArg E s hs x)) - (w : Q → M) (E.q x))
            = -(x • (φ : N → M) (liftArg E s hs y)) + (φ : N → M) (liftArg E s hs (x * y))
              - (φ : N → M) (liftArg E s hs x)
              - (x • (w : Q → M) (E.q y) - (w : Q → M) (E.q (x * y)) + (w : Q → M) (E.q x))
        rw [smul_sub, smul_neg]
        abel
      have h2 : x • (w : Q → M) (E.q y) - (w : Q → M) (E.q (x * y)) + (w : Q → M) (E.q x)
          = d1Fun (G := Q) (w : Q → M) (E.q x, E.q y) := by
        simp only [d1Fun_apply, map_mul]
        rw [hcompG x]
      rw [h1, h2, ← htg, ← hW (E.q x) (E.q y)]
      abel
    refine ⟨⟨fun x : G => -((φ : N → M) (liftArg E s hs x)) - (w : Q → M) (E.q x), hgloc⟩, ?_⟩
    apply LocallyConstant.coe_inj.mp
    funext p
    obtain ⟨x, y⟩ := p
    show d1Fun (G := G)
        (fun x : G => -((φ : N → M) (liftArg E s hs x)) - (w : Q → M) (E.q x)) (x, y)
      = ((Z2Res E.q hq hcompG z : Z2 G M) : Cochain2 G M) (x, y)
    rw [Z2Res_coe, cochain2Res_apply]
    exact hpoint x y

end Work.ConCohomology

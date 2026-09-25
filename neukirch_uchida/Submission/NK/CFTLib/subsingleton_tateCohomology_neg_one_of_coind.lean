import Mathlib
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso

/-!
# Shapiro's lemma in degree `-1` for a coinduced representation

If `H ≤ G` is a subgroup of a finite group `G` and `N` is a `ℤ[H]`-module with
`Ĥ⁻¹(H, N) = 0`, then `Ĥ⁻¹(G, Coind_H^G N) = 0`: the degree `-1` case of Shapiro's
lemma, `Ĥ⁻¹(G, Coind_H^G N) ≅ Ĥ⁻¹(H, N)`.

The proof is an explicit computation of `Ĥ⁻¹` as `ker(N) / I_G M`
(`Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso`).  Reducing to
the statement that the kernel of the norm map is contained in the augmentation span, one
shows

`ker(N_M) ⊆ span {g • f - f}`  for  `M = Coind_H^G N`,

given `ker(N_N) ⊆ span {h • n - n}` for `N`.  For `f : M` with `∑_{b : G} f b = 0` one
writes `f` as a sum of "coset-supported" elements `D_r (f r)` over a transversal `r` of
the left cosets of `H` (`transv`).  Each `D_r v` differs from `D_1 v` by an element of
the augmentation span of `M`, and the sum `y = ∑_r f r` satisfies `N_N y = ∑_b f b = 0`,
so `y` lies in the augmentation span of `N` by hypothesis, whence `D_1 y` (and therefore
`f`) lies in the augmentation span of `M`.
-/

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open CategoryTheory

namespace NK.CFTLib


set_option maxHeartbeats 2000000

noncomputable def transv {G : Type} [Group G] (H : Subgroup G) (g : G) : G :=
  (Quotient.out (QuotientGroup.mk (s := H) g⁻¹))⁻¹

lemma transv_mul_inv_mem {G : Type} [Group G] (H : Subgroup G) (g : G) :
    g * (transv H g)⁻¹ ∈ H := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g⁻¹
  have h1 : transv H g = (h : G)⁻¹ * g := by rw [transv, hh, mul_inv_rev, inv_inv]
  have h2 : g * (transv H g)⁻¹ = (h : G) := by rw [h1]; group
  rw [h2]; exact h.2

lemma transv_spec {G : Type} [Group G] (H : Subgroup G) (g : G) :
    ∃ h : H, g = (h : G) * transv H g :=
  ⟨⟨g * (transv H g)⁻¹, transv_mul_inv_mem H g⟩, by group⟩

lemma transv_eq_of_mul_eq {G : Type} [Group G] (H : Subgroup G) {r r' : G}
    (hr : r ∈ Set.range (transv H)) (hr' : r' ∈ Set.range (transv H)) (h h' : H)
    (hh : (h : G) * r = (h' : G) * r') : r = r' := by
  obtain ⟨a, rfl⟩ := hr
  obtain ⟨b, rfl⟩ := hr'
  have key : ∀ x : G, ∃ k : H, transv H x = (k : G)⁻¹ * x := by
    intro x
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H x⁻¹
    exact ⟨k, by rw [transv, hk, mul_inv_rev, inv_inv]⟩
  obtain ⟨ka, hka⟩ := key a
  obtain ⟨kb, hkb⟩ := key b
  have hh' : (h : G) * ((ka : G)⁻¹ * a) = (h' : G) * ((kb : G)⁻¹ * b) := by
    rw [← hka, ← hkb]; exact hh
  have hb : ∃ k0 : H, b = (k0 : G) * a := by
    refine ⟨kb * h'⁻¹ * h * ka⁻¹, ?_⟩
    have h2 : b = (kb : G) * ((h' : G)⁻¹ * ((h : G) * ((ka : G)⁻¹ * a))) := by
      rw [hh']; group
    rw [h2]; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  obtain ⟨k0, hk0⟩ := hb
  have hmk : QuotientGroup.mk (s := H) a⁻¹ = QuotientGroup.mk (s := H) b⁻¹ := by
    rw [QuotientGroup.eq]; rw [hk0]; group
    simpa using Subgroup.inv_mem H k0.2
  have hout : Quotient.out (QuotientGroup.mk (s := H) a⁻¹) = Quotient.out (QuotientGroup.mk (s := H) b⁻¹) := by rw [hmk]
  show (Quotient.out (QuotientGroup.mk (s := H) a⁻¹))⁻¹ = (Quotient.out (QuotientGroup.mk (s := H) b⁻¹))⁻¹
  rw [hout]

lemma mem_closure_of_mem_span {V : Type} [AddCommGroup V] (hV : Module ℤ V) {B : Set V} {y : V}
    (h : y ∈ @Submodule.span ℤ V Int.instSemiring _ hV B) : y ∈ AddSubgroup.closure B := by
  have hinst : hV = AddCommGroup.toIntModule V := Subsingleton.elim _ _
  subst hinst
  exact (Submodule.span_int_eq_addSubgroupClosure B).le ((Submodule.mem_toAddSubgroup _).mpr h)

/-! ## The two directions of the low degree description of `Ĥ⁻¹`

`Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso` identifies
`Ĥ⁻¹(G, V)` with `ker(N) / I_G V`, where `N = ∑_{g : G} ρ g` is the norm and `I_G V` is
the augmentation span `span {ρ g v - v}` (`= Representation.Coinvariants.ker ρ`).  The two
lemmas below unpack this into its two directions, in the form that is convenient for
vanishing arguments: a representation has trivial `Ĥ⁻¹` if and only if the kernel of its
norm map is contained in its augmentation span.
-/

/-- **Vanishing of `Ĥ⁻¹` in terms of the norm map.**  If `Ĥ⁻¹(G, V) = 0` then the kernel
of the norm map is contained in the augmentation span (the kernel of the coinvariant
projection). -/
theorem le_coinvariantsKer_of_subsingleton {G : Type} [Group G] [Fintype G]
    {V : Type} [AddCommGroup V] [Module ℤ V] (ρ : Representation ℤ G V)
    (h : Subsingleton (tateCohomology (Rep.of ρ) (-1))) :
    LinearMap.ker ρ.norm ≤ Representation.Coinvariants.ker ρ := by
  letI : Module ℤ ↥(LinearMap.ker (Representation.norm ρ)) :=
    (LinearMap.ker (Representation.norm ρ)).module
  obtain ⟨e⟩ := Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso ρ
  haveI hsub : Subsingleton ((LinearMap.ker (Representation.norm ρ)) ⧸
      (Submodule.comap (LinearMap.ker (Representation.norm ρ)).subtype
        (Submodule.span ℤ (Set.range fun p : G × V => ρ p.1 p.2 - p.2)))) :=
    e.symm.injective.subsingleton
  have htop := Submodule.Quotient.subsingleton_iff.mp hsub
  intro x hx
  have hmem : (⟨x, hx⟩ : LinearMap.ker (Representation.norm ρ)) ∈
      (Submodule.comap (LinearMap.ker (Representation.norm ρ)).subtype
        (Submodule.span ℤ (Set.range fun p : G × V => ρ p.1 p.2 - p.2))) := by
    rw [htop]; exact Submodule.mem_top
  simpa [Representation.Coinvariants.ker] using hmem

/-- **Vanishing of `Ĥ⁻¹` in terms of the norm map**, converse direction: if the kernel of
the norm map is contained in the augmentation span then `Ĥ⁻¹(G, V) = 0`. -/
theorem subsingleton_tateCohomology_neg_one_of_le_coinvariantsKer {G : Type} [Group G]
    [Fintype G] {V : Type} [AddCommGroup V] [Module ℤ V] (ρ : Representation ℤ G V)
    (h : LinearMap.ker ρ.norm ≤ Representation.Coinvariants.ker ρ) :
    Subsingleton (tateCohomology (Rep.of ρ) (-1)) := by
  letI : Module ℤ ↥(LinearMap.ker (Representation.norm ρ)) :=
    (LinearMap.ker (Representation.norm ρ)).module
  obtain ⟨e⟩ := Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_one_iso ρ
  have htop : (Submodule.comap (LinearMap.ker (Representation.norm ρ)).subtype
      (Submodule.span ℤ (Set.range fun p : G × V => ρ p.1 p.2 - p.2))) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    rw [Submodule.mem_comap]
    exact h x.2
  rw [Equiv.subsingleton_congr e.toEquiv, Submodule.Quotient.subsingleton_iff, htop]

theorem subsingleton_tateCohomology_neg_one_of_coind {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] (N : Rep ℤ H)
    (h : Subsingleton (tateCohomology N (-1))) :
    Subsingleton (tateCohomology (Rep.coind H.subtype N) (-1)) := by
  classical
  letI : Module ℤ N.V := N.hV2
  let M : Rep ℤ G := Rep.coind H.subtype N
  letI : Module ℤ M.V := M.hV2
  -- (A) hypothesis in kernel form for N
  have hkerN : LinearMap.ker N.ρ.norm ≤ Representation.Coinvariants.ker N.ρ :=
    le_coinvariantsKer_of_subsingleton N.ρ h
  -- (B) kernel form for the coinduced module
  have hkerM : LinearMap.ker M.ρ.norm ≤ Representation.Coinvariants.ker M.ρ := by
    intro f hf
    have hact : ∀ (g : G) (y : M.V) (b : G),
        ((M.ρ g) y : G → N.V) b = (y : G → N.V) (b * g) := fun g y b => rfl
    have hmem : ∀ (y : M.V) (g : H) (b : G),
        (y : G → N.V) ((g : G) * b) = N.ρ g ((y : G → N.V) b) :=
      fun y g b => (Representation.mem_coindV H.subtype N.ρ (y : G → N.V)).mp y.2 g b
    have hsum0 : (∑ b : G, (f : G → N.V) b) = 0 := by
      have h1 : (M.ρ.norm f : G → N.V) 1 = 0 := by rw [hf]; rfl
      have h2 : (M.ρ.norm f : G → N.V) 1 = ∑ b : G, (f : G → N.V) b := by
        rw [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [hact]
        simp
      rw [h2] at h1
      exact h1
    -- the element D1
    let D1fun : N.V → M.V := fun v =>
      ⟨fun a => if ha : a ∈ H then N.ρ ⟨a, ha⟩ v else 0, by
        rw [Representation.mem_coindV]
        intro g a
        by_cases ha : a ∈ H
        · have hga : H.subtype g * a ∈ H := H.mul_mem g.2 ha
          simp only [dif_pos ha, dif_pos hga]
          have hsub : (⟨H.subtype g * a, hga⟩ : H) = g * ⟨a, ha⟩ := Subtype.ext rfl
          rw [hsub, map_mul]
          rfl
        · have hga : ¬ (H.subtype g * a ∈ H) := fun hc => ha (by
            have h2 := H.mul_mem (Subgroup.inv_mem H g.2) hc
            simpa using h2)
          simp only [dif_neg ha, dif_neg hga, map_zero]⟩
    have hD1add : ∀ v w : N.V, D1fun (v + w) = D1fun v + D1fun w := by
      intro v w
      apply Subtype.ext
      funext a
      show (if ha : a ∈ H then N.ρ ⟨a, ha⟩ (v + w) else 0)
        = (if ha : a ∈ H then N.ρ ⟨a, ha⟩ v else 0)
          + (if ha : a ∈ H then N.ρ ⟨a, ha⟩ w else 0)
      by_cases ha : a ∈ H
      · rw [dif_pos ha, dif_pos ha, dif_pos ha, map_add]
      · rw [dif_neg ha, dif_neg ha, dif_neg ha, add_zero]
    have hD1zero : D1fun 0 = 0 := by
      apply Subtype.ext
      funext a
      simp only [D1fun, Submodule.coe_zero, Pi.zero_apply]
      by_cases ha : a ∈ H
      · rw [dif_pos ha, map_zero]
      · rw [dif_neg ha]
    let D1 : N.V →+ M.V := { toFun := D1fun, map_zero' := hD1zero, map_add' := hD1add }
    have D1_apply : ∀ (v : N.V) (a : G),
        (D1 v : G → N.V) a = if ha : a ∈ H then N.ρ ⟨a, ha⟩ v else 0 := fun v a => rfl
    have hD1_equivar : ∀ (g : H) (v : N.V), D1 (N.ρ g v) = M.ρ g (D1 v) := by
      intro g v
      apply Subtype.ext
      funext a
      have hact' : ((M.ρ g) (D1 v) : G → N.V) a = (D1 v : G → N.V) (a * g) := rfl
      rw [hact', D1_apply, D1_apply]
      by_cases ha : a ∈ H
      · have hga : a * (g : G) ∈ H := H.mul_mem ha g.2
        simp only [dif_pos ha, dif_pos hga]
        have hsub : (⟨a * (g : G), hga⟩ : H) = ⟨a, ha⟩ * g := Subtype.ext rfl
        rw [hsub, map_mul]
        rfl
      · have hga : ¬ (a * (g : G) ∈ H) := fun hc => ha (by
          have h2 := H.mul_mem hc (Subgroup.inv_mem H g.2)
          simpa using h2)
        simp only [dif_neg ha, dif_neg hga]
    -- transversal
    let R : Finset G := Finset.univ.image (transv H)
    have hmemR : ∀ (a r : G), r ∈ R → (a * r⁻¹ ∈ H ↔ r = transv H a) := by
      intro a r hr
      constructor
      · intro hh
        obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hr
        obtain ⟨ha, hha⟩ := transv_spec H a
        have h1 : ((⟨a * r⁻¹, hh⟩ : ↥H) : G) * r = a := by
          rw [show ((⟨a * r⁻¹, hh⟩ : ↥H) : G) = a * r⁻¹ from rfl]; group
        have hbr : ((⟨a * r⁻¹, hh⟩ : ↥H) : G) * r = (ha : G) * transv H a := by
          rw [h1]; exact hha
        exact transv_eq_of_mul_eq H ⟨b, hb⟩ ⟨a, rfl⟩ ⟨a * r⁻¹, hh⟩ ha hbr
      · intro he
        rw [he]
        exact transv_mul_inv_mem H a
    -- decomposition of f
    have hdecomp : f = ∑ r : {x : G // x ∈ R}, M.ρ ((r : G))⁻¹ (D1 ((f : G → N.V) (r : G))) := by
      apply Subtype.ext
      funext a
      rw [Submodule.coe_sum, Finset.sum_apply]
      have hRa : transv H a ∈ R := Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
      rw [Finset.sum_eq_single (⟨transv H a, hRa⟩ : {x : G // x ∈ R})]
      · rw [hact, D1_apply, dif_pos (transv_mul_inv_mem H a)]
        obtain ⟨ha, hha⟩ := transv_spec H a
        have hcoeeq : (⟨a * (transv H a)⁻¹, transv_mul_inv_mem H a⟩ : H) = ha := by
          apply Subtype.ext
          have h3 := congrArg (fun x : G => x * (transv H a)⁻¹) hha
          simpa [mul_assoc] using h3
        rw [hcoeeq, ← hmem f ha (transv H a)]
        exact congrArg (f : G → N.V) hha
      · intro r _ hne
        rw [hact, D1_apply]
        have hneg : ¬ (a * ((r : G))⁻¹ ∈ H) := fun hh =>
          hne (Subtype.ext ((hmemR a (r : G) r.2).mp hh))
        rw [dif_neg hneg]
      · intro hmemt
        exact absurd (Finset.mem_univ _) hmemt
    -- the sum of values
    set y : N.V := ∑ r : {x : G // x ∈ R}, (f : G → N.V) (r : G) with hydef
    have hnormy : N.ρ.norm y = ∑ b : G, (f : G → N.V) b := by
      have h1 : N.ρ.norm y
          = ∑ h : H, ∑ r : {x : G // x ∈ R}, N.ρ h ((f : G → N.V) (r : G)) := by
        rw [Representation.norm, LinearMap.sum_apply, hydef]
        refine Finset.sum_congr rfl fun h _ => ?_
        exact map_sum (N.ρ h) (fun r : {x : G // x ∈ R} => (f : G → N.V) (r : G)) Finset.univ
      have h2 : (∑ h : H, ∑ r : {x : G // x ∈ R}, N.ρ h ((f : G → N.V) (r : G)))
          = ∑ h : H, ∑ r : {x : G // x ∈ R}, (f : G → N.V) ((h : G) * (r : G)) := by
        refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun r _ => ?_
        exact (hmem f h (r : G)).symm
      have h3 : (∑ h : H, ∑ r : {x : G // x ∈ R}, (f : G → N.V) ((h : G) * (r : G)))
          = ∑ b : G, (f : G → N.V) b := by
        rw [← Fintype.sum_prod_type (f := fun p : H × {x : G // x ∈ R} =>
          (f : G → N.V) ((p.1 : G) * (p.2 : G)))]
        refine Finset.sum_bij (fun p _ => ((p.1 : G) * (p.2 : G))) ?_ ?_ ?_ ?_
        · intro p _; exact Finset.mem_univ _
        · intro p _ q _ hpq
          have hp : (p.2 : G) ∈ Set.range (transv H) := by
            obtain ⟨c, -, hc⟩ := Finset.mem_image.mp p.2.2
            exact ⟨c, hc⟩
          have hq : (q.2 : G) ∈ Set.range (transv H) := by
            obtain ⟨c, -, hc⟩ := Finset.mem_image.mp q.2.2
            exact ⟨c, hc⟩
          have h2' := transv_eq_of_mul_eq H hp hq p.1 q.1 hpq
          have h1' : (p.1 : G) = (q.1 : G) := by
            apply mul_right_cancel (b := (q.2 : G))
            rw [h2'] at hpq
            exact hpq
          exact Prod.ext (Subtype.ext h1') (Subtype.ext h2')
        · intro b _
          obtain ⟨hb, hhb⟩ := transv_spec H b
          exact ⟨(hb, ⟨transv H b, Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩⟩),
            Finset.mem_univ _, hhb.symm⟩
        · intro p _; rfl
      rw [h1, h2, h3]
    have hyker : y ∈ LinearMap.ker N.ρ.norm := by
      rw [LinearMap.mem_ker, hnormy, hsum0]
    have hycoin : y ∈ Representation.Coinvariants.ker N.ρ := hkerN hyker
    have hcl : y ∈ AddSubgroup.closure (Set.range fun p : H × N.V => N.ρ p.1 p.2 - p.2) := by
      have h2 := hycoin
      rw [Representation.Coinvariants.ker] at h2
      exact mem_closure_of_mem_span (inferInstance : Module ℤ N.V) h2
    have hD1span : ∀ x : N.V, x ∈ AddSubgroup.closure (Set.range fun p : H × N.V =>
        N.ρ p.1 p.2 - p.2) → D1 x ∈ Representation.Coinvariants.ker M.ρ := by
      intro x hx
      exact AddSubgroup.closure_induction
        (p := fun x _ => D1 x ∈ Representation.Coinvariants.ker M.ρ)
        (fun b hb => by
          obtain ⟨⟨h, v⟩, rfl⟩ := hb
          have heq : D1 (N.ρ h v - v) = M.ρ h (D1 v) - D1 v := by rw [map_sub, hD1_equivar]
          rw [heq]
          exact Representation.Coinvariants.sub_mem_ker (ρ := M.ρ) h (D1 v))
        (by rw [map_zero]; exact Submodule.zero_mem _)
        (fun a₁ a₂ _ _ ih₁ ih₂ => by rw [map_add]; exact Submodule.add_mem _ ih₁ ih₂)
        (fun a _ ih => by rw [map_neg]; exact Submodule.neg_mem _ ih)
        hx
    have hD1y : D1 y ∈ Representation.Coinvariants.ker M.ρ := hD1span y hcl
    have hB : (∑ r : {x : G // x ∈ R}, D1 ((f : G → N.V) (r : G))) = D1 y := by
      rw [hydef]
      exact (map_sum D1 (fun r : {x : G // x ∈ R} => (f : G → N.V) (r : G)) Finset.univ).symm
    have hsplit : (∑ r : {x : G // x ∈ R}, M.ρ ((r : G))⁻¹ (D1 ((f : G → N.V) (r : G))))
        = (∑ r : {x : G // x ∈ R}, (M.ρ ((r : G))⁻¹ (D1 ((f : G → N.V) (r : G)))
            - D1 ((f : G → N.V) (r : G)))) + D1 y := by
      rw [Finset.sum_sub_distrib, hB, sub_add_cancel]
    rw [hdecomp, hsplit]
    exact Submodule.add_mem _
      (Submodule.sum_mem _ fun r _ =>
        Representation.Coinvariants.sub_mem_ker (ρ := M.ρ) ((r : G)⁻¹)
          (D1 ((f : G → N.V) (r : G))))
      hD1y
  -- (C) conclude
  exact subsingleton_tateCohomology_neg_one_of_le_coinvariantsKer M.ρ hkerM

end NK.CFTLib

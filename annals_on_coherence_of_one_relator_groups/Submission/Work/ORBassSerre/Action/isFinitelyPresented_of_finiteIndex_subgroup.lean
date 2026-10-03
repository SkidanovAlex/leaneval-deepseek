import Mathlib
import Submission.Work.ORBassSerre.Action.Basic

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.ORBassSerre.Action

variable {G : Type*} [Group G]

/-- The type of right cosets of a subgroup `H` of `G`, as the quotient of `G` by the right
action of `H`.  Its elements are the right cosets `H · g`. -/
abbrev RCosets (H : Subgroup G) : Type _ := Quotient (QuotientGroup.rightRel H)

namespace RCosets

variable (H : Subgroup G)

noncomputable instance instFintype [H.FiniteIndex] : Fintype (RCosets H) :=
  letI : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex (H := H)
  QuotientGroup.fintypeQuotientRightRel (s := H)

/-- The right coset `H · 1 = H`. -/
def base : RCosets H := Quotient.mk (QuotientGroup.rightRel H) (1 : G)

lemma out_base_mem : Quotient.out (base H) ∈ H := by
  have hh := @Quotient.mk_out G (QuotientGroup.rightRel H) (1 : G)
  rw [QuotientGroup.rightRel_apply, one_mul, inv_mem_iff] at hh
  exact hh

/-- A section of the right coset quotient `G → RCosets H`, normalised by `rep H (base H) = 1`. -/
noncomputable def rep (q : RCosets H) : G :=
  (Quotient.out (base H))⁻¹ * Quotient.out q

@[simp] lemma rep_base : rep H (base H) = 1 := by
  rw [rep, inv_mul_cancel]

lemma mk_rep (q : RCosets H) : Quotient.mk (QuotientGroup.rightRel H) (rep H q) = q := by
  conv_rhs => rw [← Quotient.out_eq q]
  rw [Quotient.eq'', QuotientGroup.rightRel_apply]
  show Quotient.out q * (rep H q)⁻¹ ∈ H
  rw [rep]
  have h : Quotient.out q * ((Quotient.out (base H))⁻¹ * Quotient.out q)⁻¹
      = Quotient.out (base H) := by group
  rw [h]
  exact out_base_mem H

/-- An element `g` lies in the right coset `q` iff `g * (rep H q)⁻¹ ∈ H`. -/
lemma mul_rep_inv_mem {g : G} {q : RCosets H}
    (hq : Quotient.mk (QuotientGroup.rightRel H) g = q) : g * (rep H q)⁻¹ ∈ H := by
  have h1 : Quotient.mk (QuotientGroup.rightRel H) (rep H q)
      = Quotient.mk (QuotientGroup.rightRel H) g := by rw [mk_rep H q, hq]
  rw [Quotient.eq'', QuotientGroup.rightRel_apply] at h1
  exact h1

/-- The decomposition `g = h · rep H q` of an element of `G` with second factor in the chosen
system of representatives of the right cosets. -/
noncomputable def dec (g : G) : H × RCosets H :=
  (⟨g * (rep H (Quotient.mk (QuotientGroup.rightRel H) g))⁻¹, mul_rep_inv_mem H rfl⟩,
    Quotient.mk (QuotientGroup.rightRel H) g)

lemma dec_val (g : G) : ((dec H g).1 : G) * rep H (dec H g).2 = g := by
  show g * (rep H (Quotient.mk (QuotientGroup.rightRel H) g))⁻¹
      * rep H (Quotient.mk (QuotientGroup.rightRel H) g) = g
  rw [mul_assoc, inv_mul_cancel, mul_one]

lemma dec_rep (q : RCosets H) : dec H (rep H q) = (1, q) := by
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    show rep H q * (rep H (Quotient.mk (QuotientGroup.rightRel H) (rep H q)))⁻¹ = ((1 : H) : G)
    rw [mk_rep H q]
    simp
  · show Quotient.mk (QuotientGroup.rightRel H) (rep H q) = q
    exact mk_rep H q

/-- The quotient map on right cosets is invariant under left multiplication by elements of `H`. -/
lemma mk_mul_left (h : H) (g : G) :
    Quotient.mk (QuotientGroup.rightRel H) ((h : G) * g)
      = Quotient.mk (QuotientGroup.rightRel H) g := by
  rw [Quotient.eq'', QuotientGroup.rightRel_apply]
  have hh : g * ((h : G) * g)⁻¹ = ((h : G))⁻¹ := by group
  rw [hh]
  exact inv_mem h.2

lemma dec_mul_left (h : H) (g : G) :
    dec H ((h : G) * g) = (h * (dec H g).1, (dec H g).2) := by
  have hmk := mk_mul_left H h g
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    show (h : G) * g * (rep H (Quotient.mk (QuotientGroup.rightRel H) ((h : G) * g)))⁻¹
        = (h : G) * (g * (rep H (Quotient.mk (QuotientGroup.rightRel H) g))⁻¹)
    rw [hmk]
    group
  · show Quotient.mk (QuotientGroup.rightRel H) ((h : G) * g)
        = Quotient.mk (QuotientGroup.rightRel H) g
    exact hmk

lemma dec_unique {a b : H} {q q' : RCosets H}
    (h : (a : G) * rep H q = (b : G) * rep H q') : a = b ∧ q = q' := by
  have hq : q = q' := by
    have h1 : Quotient.mk (QuotientGroup.rightRel H) (rep H q)
        = Quotient.mk (QuotientGroup.rightRel H) (rep H q') := by
      have h2 := congrArg (fun x => Quotient.mk (QuotientGroup.rightRel H) x) h
      simpa [mk_mul_left] using h2
    rwa [mk_rep H q, mk_rep H q'] at h1
  subst hq
  have hab : (a : G) = (b : G) := mul_right_cancel h
  exact ⟨Subtype.ext hab, rfl⟩

lemma dec_eq_of {g : G} {a : H} {q : RCosets H} (hg : g = (a : G) * rep H q) :
    dec H g = (a, q) := by
  obtain ⟨h1, h2⟩ := dec_unique H (a := (dec H g).1) (b := a) (q := (dec H g).2) (q' := q)
    ((dec_val H g).trans hg)
  subst h1
  subst h2
  rfl

lemma dec_one : dec H (1 : G) = (1, base H) := by
  refine dec_eq_of H ?_
  simp

/-- From an identification of the decomposition of `g` one reads off the equality `g = h · rep q`. -/
lemma dec_val_of {g : G} {κ : H} {q : RCosets H} (h : dec H g = (κ, q)) :
    (κ : G) * rep H q = g := by
  have h1 : (dec H g).1 = κ := by rw [h]
  have h2 : (dec H g).2 = q := by rw [h]
  rw [← h1, ← h2]
  exact dec_val H g

/-- Decomposition of a product of two elements already in normal form. -/
lemma dec_mul_reps {h h' : H} {q q' : RCosets H} {κ : H} {q'' : RCosets H} {κ' : H}
    {q''' : RCosets H} (h1 : dec H (rep H q * (h' : G)) = (κ, q''))
    (h2 : dec H (rep H q'' * rep H q') = (κ', q''')) :
    dec H (((h : G) * rep H q) * ((h' : G) * rep H q')) = (h * κ * κ', q''') := by
  refine dec_eq_of H ?_
  have hv : (κ : G) * rep H q'' = rep H q * (h' : G) := dec_val_of H h1
  have hv' : (κ' : G) * rep H q''' = rep H q'' * rep H q' := dec_val_of H h2
  calc ((h : G) * rep H q) * ((h' : G) * rep H q')
      = (h : G) * (rep H q * (h' : G)) * rep H q' := by group
    _ = (h : G) * ((κ : G) * rep H q'') * rep H q' := by rw [← hv]
    _ = (h : G) * ((κ : G) * (rep H q'' * rep H q')) := by group
    _ = (h : G) * ((κ : G) * ((κ' : G) * rep H q''')) := by rw [← hv']
    _ = ((h * κ * κ' : H) : G) * rep H q''' := by push_cast; group

/-- Decomposition of `rep H q * (h * u)` for an element `u` of `G` whose decomposition after
`rep H q''` is known. -/
lemma dec_mul_single {h : H} {q : RCosets H} {u : G} {κ κ₁ : H} {q'' q₁ : RCosets H}
    (h1 : dec H (rep H q * (h : G)) = (κ, q'')) (h2 : dec H (rep H q'' * u) = (κ₁, q₁)) :
    dec H (rep H q * ((h : G) * u)) = (κ * κ₁, q₁) := by
  refine dec_eq_of H ?_
  have hv : (κ : G) * rep H q'' = rep H q * (h : G) := dec_val_of H h1
  have hv₁ : (κ₁ : G) * rep H q₁ = rep H q'' * u := dec_val_of H h2
  calc rep H q * ((h : G) * u)
      = rep H q * (h : G) * u := by group
    _ = ((κ : G) * rep H q'') * u := by rw [← hv]
    _ = (κ : G) * (rep H q'' * u) := by group
    _ = (κ : G) * ((κ₁ : G) * rep H q₁) := by rw [← hv₁]
    _ = ((κ * κ₁ : H) : G) * rep H q₁ := by push_cast; group

end RCosets

section Aux

variable (H : Subgroup G)

/-- The free product `H ∗ F(Ω)`, where `Ω` is the set of right cosets of `H` in `G`. -/
abbrev FreeProd : Type _ := Monoid.Coprod H (FreeGroup (RCosets H))

/-- The homomorphism `H ∗ F(Ω) →* G` sending `H` into `G` and the free generator attached to a
coset `q` to the chosen representative `rep H q`. -/
noncomputable def psi : FreeProd H →* G :=
  Monoid.Coprod.lift (Subgroup.subtype H) (FreeGroup.lift (fun q : RCosets H => RCosets.rep H q))

/-- The natural map `H →* H ∗ F(Ω)`. -/
noncomputable def iotaFree : H →* FreeProd H := Monoid.Coprod.inl

/-- The generator of `H ∗ F(Ω)` attached to a right coset `q`. -/
noncomputable def tFree (q : RCosets H) : FreeProd H := Monoid.Coprod.inr (FreeGroup.of q)

@[simp] lemma psi_iotaFree (h : H) : psi H (iotaFree H h) = h := by
  rw [psi, iotaFree, Monoid.Coprod.lift_apply_inl]
  rfl

@[simp] lemma psi_tFree (q : RCosets H) : psi H (tFree H q) = RCosets.rep H q := by
  rw [psi, tFree, Monoid.Coprod.lift_apply_inr, FreeGroup.lift_apply_of]

/-- The relation expressing `t q · y = (h-part) · t (coset-part)` for the decomposition of
`rep H q * y`. -/
noncomputable def relA (q : RCosets H) (y : H) : FreeProd H :=
  (tFree H q * iotaFree H y) *
    (iotaFree H (RCosets.dec H (RCosets.rep H q * (y : G))).1
      * tFree H (RCosets.dec H (RCosets.rep H q * (y : G))).2)⁻¹

/-- The relation expressing `t q · t q' = (h-part) · t (coset-part)` for the decomposition of
`rep H q * rep H q'`. -/
noncomputable def relB (q q' : RCosets H) : FreeProd H :=
  (tFree H q * tFree H q') *
    (iotaFree H (RCosets.dec H (RCosets.rep H q * RCosets.rep H q')).1
      * tFree H (RCosets.dec H (RCosets.rep H q * RCosets.rep H q')).2)⁻¹

/-- The relation `t (base H) = 1`. -/
noncomputable def relC : FreeProd H := tFree H (RCosets.base H)

lemma psi_relA (q : RCosets H) (y : H) : psi H (relA H q y) = 1 := by
  obtain ⟨κ, q', hdec⟩ : ∃ κ q', RCosets.dec H (RCosets.rep H q * (y : G)) = (κ, q') :=
    ⟨_, _, rfl⟩
  have h1 : (RCosets.dec H (RCosets.rep H q * (y : G))).1 = κ := by rw [hdec]
  have h2 : (RCosets.dec H (RCosets.rep H q * (y : G))).2 = q' := by rw [hdec]
  have hv : (κ : G) * RCosets.rep H q' = RCosets.rep H q * (y : G) := by
    rw [← h1, ← h2]; exact RCosets.dec_val H _
  simp only [relA, hdec, map_mul, map_inv, psi_tFree, psi_iotaFree]
  rw [hv]
  group

lemma psi_relB (q q' : RCosets H) : psi H (relB H q q') = 1 := by
  obtain ⟨κ, q'', hdec⟩ : ∃ κ q'', RCosets.dec H (RCosets.rep H q * RCosets.rep H q') = (κ, q'') :=
    ⟨_, _, rfl⟩
  have h1 : (RCosets.dec H (RCosets.rep H q * RCosets.rep H q')).1 = κ := by rw [hdec]
  have h2 : (RCosets.dec H (RCosets.rep H q * RCosets.rep H q')).2 = q'' := by rw [hdec]
  have hv : (κ : G) * RCosets.rep H q'' = RCosets.rep H q * RCosets.rep H q' := by
    rw [← h1, ← h2]; exact RCosets.dec_val H _
  simp only [relB, hdec, map_mul, map_inv, psi_tFree, psi_iotaFree]
  rw [hv]
  group

lemma psi_relC : psi H (relC H) = 1 := by
  rw [relC, psi_tFree, RCosets.rep_base]

/-- The images of the two factors generate the free product. -/
lemma closure_range_iotaFree_union_tFree :
    Subgroup.closure (Set.range (iotaFree H) ∪ Set.range (tFree H)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← Monoid.Coprod.closure_range_inl_union_inr (G := H) (H := FreeGroup (RCosets H))]
  rw [Subgroup.closure_le]
  rintro x (hx | hx)
  · exact Subgroup.subset_closure (Or.inl hx)
  · obtain ⟨y, rfl⟩ := hx
    have hy : y ∈ Subgroup.closure
        (Set.range (FreeGroup.of : RCosets H → FreeGroup (RCosets H))) := by
      rw [FreeGroup.closure_range_of]
      exact Subgroup.mem_top y
    have hmem : Monoid.Coprod.inr y ∈
        (Subgroup.closure (Set.range (FreeGroup.of : RCosets H → FreeGroup (RCosets H)))).map
          (Monoid.Coprod.inr : FreeGroup (RCosets H) →* FreeProd H) :=
      ⟨y, hy, rfl⟩
    rw [MonoidHom.map_closure] at hmem
    have himg : Monoid.Coprod.inr ''
        Set.range (FreeGroup.of : RCosets H → FreeGroup (RCosets H)) = Set.range (tFree H) := by
      rw [← Set.range_comp]
      rfl
    rw [himg] at hmem
    exact Subgroup.closure_mono Set.subset_union_right hmem

end Aux

/-- A group with a finitely presented subgroup of finite index is finitely presented. -/
theorem isFinitelyPresented_of_finiteIndex_subgroup {G : Type*} [Group G] (H : Subgroup G)
    [H.FiniteIndex] [h : Group.IsFinitelyPresented H] : Group.IsFinitelyPresented G := by
  classical
  obtain ⟨n, φ, hφ, S, hSfin, hScl⟩ := h.out
  -- `H` is finitely generated, with a finite generating set closed under inversion.
  have hFG : Group.FG H := by
    rw [Group.fg_iff]
    refine ⟨Set.range (fun i : Fin n => φ (FreeGroup.of i)), ?_, Set.finite_range _⟩
    have h1 : Subgroup.map φ
        (Subgroup.closure (Set.range (FreeGroup.of : Fin n → FreeGroup (Fin n))))
        = Subgroup.closure (Set.range (fun i : Fin n => φ (FreeGroup.of i))) := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      rfl
    rw [← h1, FreeGroup.closure_range_of, Subgroup.map_top_of_surjective φ hφ]
  obtain ⟨m, s, -, hsclos⟩ := Group.fg_iff'.mp hFG
  set s' : Finset H := s ∪ s.image (fun y => y⁻¹) with hs'def
  have hle_ss : Subgroup.closure (↑s : Set H) ≤ Subgroup.closure (↑s' : Set H) := by
    rw [Subgroup.closure_le]
    intro y hy
    exact Subgroup.subset_closure (by rw [hs'def]; exact Finset.mem_union_left _ hy)
  have hs'clos : Subgroup.closure (↑s' : Set H) = ⊤ := by
    apply le_antisymm le_top
    rw [← hsclos]
    exact hle_ss
  have hs'inv : ∀ y ∈ s', y⁻¹ ∈ s' := by
    intro y hy
    rw [hs'def] at hy ⊢
    rcases Finset.mem_union.mp hy with hy | hy
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    · obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
      have hyz : y⁻¹ = z := by rw [← hzy]; simp
      rw [hyz]
      exact Finset.mem_union_left _ hz
  -- the finite set of relations
  set Rel : Set (FreeProd H) :=
    (fun p : RCosets H × s' => relA H p.1 p.2) '' (Set.univ : Set (RCosets H × s'))
      ∪ (fun p : RCosets H × RCosets H => relB H p.1 p.2) ''
          (Set.univ : Set (RCosets H × RCosets H))
      ∪ {relC H} with hReldef
  have hRelFin : Rel.Finite := by
    rw [hReldef]
    exact (((Set.toFinite (Set.univ : Set (RCosets H × s'))).image
        (fun p : RCosets H × s' => relA H p.1 p.2)).union
      ((Set.toFinite (Set.univ : Set (RCosets H × RCosets H))).image
        (fun p : RCosets H × RCosets H => relB H p.1 p.2))).union
      (Set.finite_singleton (relC H))
  set N : Subgroup (FreeProd H) := Subgroup.normalClosure Rel with hNdef
  have hle : N ≤ (psi H).ker := by
    rw [hNdef]
    apply Subgroup.normalClosure_le_normal
    rintro r hr
    rw [hReldef] at hr
    change psi H r = 1
    rcases hr with (hr | hr) | hr
    · obtain ⟨p, -, rfl⟩ := hr
      exact psi_relA H p.1 p.2
    · obtain ⟨p, -, rfl⟩ := hr
      exact psi_relB H p.1 p.2
    · rw [Set.mem_singleton_iff] at hr
      subst hr
      exact psi_relC H
  have hNnormal : N.Normal := by rw [hNdef]; exact Subgroup.normalClosure_normal
  let π : FreeProd H ⧸ N →* G := QuotientGroup.lift N (psi H) hle
  have hπ_mk (x : FreeProd H) : π (QuotientGroup.mk' N x) = psi H x := rfl
  let ι : H →* FreeProd H ⧸ N := (QuotientGroup.mk' N).comp (iotaFree H)
  let T : RCosets H → FreeProd H ⧸ N := fun q => QuotientGroup.mk' N (tFree H q)
  have hι_val : ∀ h : H, ι h = QuotientGroup.mk' N (iotaFree H h) := fun h => rfl
  have hT_val : ∀ q : RCosets H, T q = QuotientGroup.mk' N (tFree H q) := fun q => rfl
  have hπ_ι (h : H) : π (ι h) = h := by rw [hι_val, hπ_mk, psi_iotaFree]
  have hπ_T (q : RCosets H) : π (T q) = RCosets.rep H q := by rw [hT_val, hπ_mk, psi_tFree]
  -- Claim A for the generators
  have hClaimA_single : ∀ (y : H) (hy : y ∈ (↑s' : Set H)) (q : RCosets H),
      T q * ι y = ι (RCosets.dec H (RCosets.rep H q * (y : G))).1
        * T (RCosets.dec H (RCosets.rep H q * (y : G))).2 := by
    intro y hy q
    have hmem : relA H q y ∈ N := by
      rw [hNdef]
      apply Subgroup.subset_normalClosure
      rw [hReldef]
      exact Or.inl (Or.inl ⟨(q, ⟨y, hy⟩), Set.mem_univ _, rfl⟩)
    have h1 : QuotientGroup.mk' N (relA H q y) = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
    simp only [relA, map_mul, map_inv, ← hT_val, ← hι_val] at h1
    rw [mul_inv_eq_one] at h1
    exact h1
  -- Claim A
  have hClaimA : ∀ h : H, ∀ q : RCosets H,
      T q * ι h = ι (RCosets.dec H (RCosets.rep H q * (h : G))).1
        * T (RCosets.dec H (RCosets.rep H q * (h : G))).2 := by
    intro h
    have hgen : h ∈ Subgroup.closure (↑s' : Set H) := by rw [hs'clos]; exact Subgroup.mem_top h
    refine Subgroup.closure_induction_right (s := (↑s' : Set H))
      (p := fun x (_ : x ∈ Subgroup.closure (↑s' : Set H)) => ∀ q : RCosets H,
          T q * ι x = ι (RCosets.dec H (RCosets.rep H q * (x : G))).1
            * T (RCosets.dec H (RCosets.rep H q * (x : G))).2) ?_ ?_ ?_ hgen
    · intro q
      have h1 : (RCosets.dec H (RCosets.rep H q * ((1 : H) : G))).1 = 1 := by
        rw [Subgroup.coe_one, mul_one, RCosets.dec_rep H q]
      have h2 : (RCosets.dec H (RCosets.rep H q * ((1 : H) : G))).2 = q := by
        rw [Subgroup.coe_one, mul_one, RCosets.dec_rep H q]
      rw [h1, h2, map_one, one_mul, mul_one]
    · intro x hx y hy IH q
      simp only [Subgroup.coe_mul]
      obtain ⟨κ, q'', hdec⟩ : ∃ κ q'', RCosets.dec H (RCosets.rep H q * (x : G)) = (κ, q'') :=
        ⟨_, _, rfl⟩
      obtain ⟨κ₁, q₁, hdec₁⟩ : ∃ κ₁ q₁, RCosets.dec H (RCosets.rep H q'' * (y : G)) = (κ₁, q₁) :=
        ⟨_, _, rfl⟩
      have hIH : T q * ι x = ι κ * T q'' := by
        have hh := IH q
        rw [hdec] at hh
        exact hh
      have hy' : T q'' * ι y = ι κ₁ * T q₁ := by
        have hh := hClaimA_single y hy q''
        rw [hdec₁] at hh
        exact hh
      have hdec₀ : RCosets.dec H (RCosets.rep H q * ((x : G) * (y : G))) = (κ * κ₁, q₁) :=
        RCosets.dec_mul_single H hdec hdec₁
      calc T q * ι (x * y)
          = T q * (ι x * ι y) := by rw [map_mul]
        _ = (T q * ι x) * ι y := by group
        _ = (ι κ * T q'') * ι y := by rw [hIH]
        _ = ι κ * (T q'' * ι y) := by group
        _ = ι κ * (ι κ₁ * T q₁) := by rw [hy']
        _ = ι (κ * κ₁) * T q₁ := by rw [map_mul]; group
        _ = ι (RCosets.dec H (RCosets.rep H q * ((x : G) * (y : G)))).1
              * T (RCosets.dec H (RCosets.rep H q * ((x : G) * (y : G)))).2 := by rw [hdec₀]
    · intro x hx y hy IH q
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      obtain ⟨κ, q'', hdec⟩ : ∃ κ q'', RCosets.dec H (RCosets.rep H q * (x : G)) = (κ, q'') :=
        ⟨_, _, rfl⟩
      obtain ⟨κ₁, q₁, hdec₁⟩ : ∃ κ₁ q₁,
          RCosets.dec H (RCosets.rep H q'' * ((y : H) : G)⁻¹) = (κ₁, q₁) := ⟨_, _, rfl⟩
      have hIH : T q * ι x = ι κ * T q'' := by
        have hh := IH q
        rw [hdec] at hh
        exact hh
      have hy' : T q'' * (ι y)⁻¹ = ι κ₁ * T q₁ := by
        have hh := hClaimA_single y⁻¹ (hs'inv y hy) q''
        rw [Subgroup.coe_inv, hdec₁, map_inv] at hh
        exact hh
      have hdec₀ : RCosets.dec H (RCosets.rep H q * ((x : G) * ((y : H) : G)⁻¹)) = (κ * κ₁, q₁) :=
        RCosets.dec_mul_single H hdec hdec₁
      calc T q * ι (x * y⁻¹)
          = T q * (ι x * (ι y)⁻¹) := by rw [map_mul, map_inv]
        _ = (T q * ι x) * (ι y)⁻¹ := by group
        _ = (ι κ * T q'') * (ι y)⁻¹ := by rw [hIH]
        _ = ι κ * (T q'' * (ι y)⁻¹) := by group
        _ = ι κ * (ι κ₁ * T q₁) := by rw [hy']
        _ = ι (κ * κ₁) * T q₁ := by rw [map_mul]; group
        _ = ι (RCosets.dec H (RCosets.rep H q * ((x : G) * ((y : H) : G)⁻¹))).1
              * T (RCosets.dec H (RCosets.rep H q * ((x : G) * ((y : H) : G)⁻¹))).2 := by
            rw [hdec₀]
  -- Claim B
  have hClaimB : ∀ q q' : RCosets H,
      T q * T q' = ι (RCosets.dec H (RCosets.rep H q * RCosets.rep H q')).1
        * T (RCosets.dec H (RCosets.rep H q * RCosets.rep H q')).2 := by
    intro q q'
    have hmem : relB H q q' ∈ N := by
      rw [hNdef]
      apply Subgroup.subset_normalClosure
      rw [hReldef]
      exact Or.inl (Or.inr ⟨(q, q'), Set.mem_univ _, rfl⟩)
    have h1 : QuotientGroup.mk' N (relB H q q') = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
    simp only [relB, map_mul, map_inv, ← hT_val, ← hι_val] at h1
    rw [mul_inv_eq_one] at h1
    exact h1
  have hTbase : T (RCosets.base H) = 1 := by
    have hmem : relC H ∈ N := by
      rw [hNdef]
      apply Subgroup.subset_normalClosure
      rw [hReldef]
      exact Or.inr (Set.mem_singleton _)
    have h1 : QuotientGroup.mk' N (relC H) = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
    rw [relC] at h1
    rwa [← hT_val] at h1
  -- the section `σ : G → H ∗ F(Ω)/N`
  let σfun : G → FreeProd H ⧸ N := fun g => ι (RCosets.dec H g).1 * T (RCosets.dec H g).2
  have hσ_mul : ∀ g g' : G, σfun (g * g') = σfun g * σfun g' := by
    intro g g'
    obtain ⟨h, q, hdec⟩ : ∃ h q, RCosets.dec H g = (h, q) := ⟨_, _, rfl⟩
    obtain ⟨h', q', hdec'⟩ : ∃ h' q', RCosets.dec H g' = (h', q') := ⟨_, _, rfl⟩
    have hg : (h : G) * RCosets.rep H q = g := RCosets.dec_val_of H hdec
    have hg' : (h' : G) * RCosets.rep H q' = g' := RCosets.dec_val_of H hdec'
    obtain ⟨κ, q'', hdecq⟩ : ∃ κ q'', RCosets.dec H (RCosets.rep H q * (h' : G)) = (κ, q'') :=
      ⟨_, _, rfl⟩
    obtain ⟨κ', q''', hdecq'⟩ : ∃ κ' q''',
        RCosets.dec H (RCosets.rep H q'' * RCosets.rep H q') = (κ', q''') := ⟨_, _, rfl⟩
    have hA : T q * ι h' = ι κ * T q'' := by
      have hh := hClaimA h' q
      rw [hdecq] at hh
      exact hh
    have hB : T q'' * T q' = ι κ' * T q''' := by
      have hh := hClaimB q'' q'
      rw [hdecq'] at hh
      exact hh
    have hdecgg : RCosets.dec H (g * g') = (h * κ * κ', q''') := by
      rw [← hg, ← hg']
      exact RCosets.dec_mul_reps H hdecq hdecq'
    show ι (RCosets.dec H (g * g')).1 * T (RCosets.dec H (g * g')).2
      = (ι (RCosets.dec H g).1 * T (RCosets.dec H g).2)
        * (ι (RCosets.dec H g').1 * T (RCosets.dec H g').2)
    rw [hdecgg, hdec, hdec']
    calc ι (h * κ * κ') * T q'''
        = ι h * (ι κ * (ι κ' * T q''')) := by rw [map_mul, map_mul]; group
      _ = ι h * (ι κ * (T q'' * T q')) := by rw [← hB]
      _ = ι h * ((ι κ * T q'') * T q') := by group
      _ = ι h * ((T q * ι h') * T q') := by rw [← hA]
      _ = (ι h * T q) * (ι h' * T q') := by group
  let σ : G →* FreeProd H ⧸ N := MonoidHom.mk' σfun hσ_mul
  have hσ_apply (g : G) : σ g = ι (RCosets.dec H g).1 * T (RCosets.dec H g).2 := rfl
  have hσ_iotafree (h : H) : σ h = ι h := by
    have hdec : RCosets.dec H (h : G) = (h, RCosets.base H) := by
      refine RCosets.dec_eq_of H ?_
      simp
    have h1 : (RCosets.dec H (h : G)).1 = h := by rw [hdec]
    have h2 : (RCosets.dec H (h : G)).2 = RCosets.base H := by rw [hdec]
    rw [hσ_apply, h1, h2, hTbase, mul_one]
  have hσ_T (q : RCosets H) : σ (RCosets.rep H q) = T q := by
    have h1 : (RCosets.dec H (RCosets.rep H q)).1 = 1 := by rw [RCosets.dec_rep H q]
    have h2 : (RCosets.dec H (RCosets.rep H q)).2 = q := by rw [RCosets.dec_rep H q]
    rw [hσ_apply, h1, h2, map_one, one_mul]
  have hπσ (g : G) : π (σ g) = g := by
    rw [hσ_apply, map_mul, hπ_ι, hπ_T, RCosets.dec_val H g]
  -- the image of `σ` generates
  have hgenq : Subgroup.closure (Set.range ι ∪ Set.range T) = ⊤ := by
    have hset : Set.range ι ∪ Set.range T
        = (QuotientGroup.mk' N) '' (Set.range (iotaFree H) ∪ Set.range (tFree H)) := by
      rw [Set.image_union]
      congr 1
      · rw [← Set.range_comp]; rfl
      · rw [← Set.range_comp]; rfl
    rw [hset, ← MonoidHom.map_closure, closure_range_iotaFree_union_tFree H,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  have hσsurj : Function.Surjective σ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgenq]
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · obtain ⟨h, rfl⟩ := hx
      exact ⟨h, hσ_iotafree h⟩
    · obtain ⟨q, rfl⟩ := hx
      exact ⟨RCosets.rep H q, hσ_T q⟩
  have hπ_inj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    obtain ⟨g, rfl⟩ := hσsurj p
    change π (σ g) = 1 at hp
    rw [hπσ g] at hp
    rw [Subgroup.mem_bot, hp, map_one]
  have hπ_ker : π.ker = ⊥ := by rw [MonoidHom.ker_eq_bot_iff]; exact hπ_inj
  have hker_le : (psi H).ker ≤ N := by
    intro x hx
    have hx1 : psi H x = 1 := MonoidHom.mem_ker.mp hx
    have hxπ : QuotientGroup.mk' N x ∈ π.ker := by
      change π (QuotientGroup.mk' N x) = 1
      rw [hπ_mk x, hx1]
    rw [hπ_ker, Subgroup.mem_bot] at hxπ
    exact (QuotientGroup.eq_one_iff x).mp hxπ
  have hNker : N = (psi H).ker := le_antisymm hle hker_le
  refine Group.IsFinitelyPresented.of_surjective (psi H) (fun g => ?_)
    ⟨Rel, hRelFin, by rw [← hNdef]; exact hNker⟩
  exact ⟨iotaFree H (RCosets.dec H g).1 * tFree H (RCosets.dec H g).2, by
    rw [map_mul, psi_iotaFree, psi_tFree, RCosets.dec_val H g]⟩

end Work.ORBassSerre.Action
